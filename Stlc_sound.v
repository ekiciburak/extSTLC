From SFL Require Import Imports Auxiliaries Terms Typecheck Eval Progress Preservation.
Require Import Coq.Strings.String.

Require Import Coq.Relations.Relations.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition step (t t': term ): Prop := beta t = Some t'.

Definition multistep := multi step.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition normal_form_a (e: term) :=
  let be := beta e in
  match be with
    | Some be' => if term_eqb be' e then true else false
    | _        => false
  end.

Definition stuck (e: term) :=
  (normal_form step) e /\ isvalue e = false.


Definition stuck_a (e: term) :=
  normal_form_a e = true /\ isvalue e = false.


Definition stuck_b (t: term) := beta t = None /\ isvalue t = false.

Theorem soundness: forall t t' T, 
  typecheck nil t = Some T /\ 
  multistep t t' -> 
  ~ stuck t'.
Proof. intros t t' T (H, H0). unfold stuck.
       induction H0; intros.
       - unfold not. intros (Hnf, Hnv).
         unfold normal_form in *. apply Hnf.
         unfold step.
         specialize (progress x T H); intros.
         destruct H0. rewrite Hnv in H0. easy.
         destruct H0. exists x0. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (preservation x y T (conj H H0)); intros.
         specialize (IHmulti H2).
         apply IHmulti. split; easy.
Qed.

Theorem soundness_R: forall n t t' T, 
  typecheck nil t = Some T /\
  evaln t n  = Some t' -> 
  ~ stuck_b t'.
Proof. unfold stuck_b, not.
       intro n.
       induction n as [| m IHn]; intros t t' T (Ha, Hb) (Hne, Hnv).
       - cbn in Hb. inversion Hb. rewrite <- H0 in *.
         specialize (progress t T Ha); intros Hp.
         destruct Hp as [ Hp | Hp].
         + rewrite Hp in Hnv. contradict Hnv; easy.
         + destruct Hp as (t'', Hp).
           rewrite Hp in Hne. contradict Hne; easy.
       - cbn in Hb.
         specialize (progress t T Ha); intros Hp.
         destruct Hp as [ Hp | Hp].
         + apply isvalue_beta in Hp.
           rewrite Hp in Hb. contradict Hb; easy.
         + destruct Hp as (e, He).
           rewrite He in Hb.
           specialize (preservation t e T (conj Ha He)); intros Hte.
           specialize (IHn e t' T (conj Hte Hb)).
           apply IHn. split; easy.
Qed.

Theorem soundness_Q: forall n t T, 
  typecheck nil t = Some T /\
  evaln t n = None -> 
  ~ stuck_b t.
Proof. intros n. unfold stuck_b.
       induction n; intros t T (H, H0).
       - unfold not. intros (Hnf, Hnv).
         specialize (progress t T H); intros.
         cbn in *. inversion H0.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (progress t T H); intros.
         destruct H1. rewrite H1 in Hnv. easy.
         destruct H1. rewrite H1 in Hnf. easy.
Qed.


Theorem soundness_a: forall t t' T, 
  typecheck nil t = Some T /\ 
  multistep t t' -> 
  ~ stuck_b t'.
Proof. intros t t' T (H, H0). unfold stuck_b.
       induction H0.
       - unfold not. intros (Hnf, Hnv).
         specialize (progress x T H); intros.
         destruct H0. rewrite H0 in Hnv. easy.
         destruct H0 as (t, Ha).
         rewrite Ha in Hnf. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (preservation x y T (conj H H0)); intros.
         specialize (IHmulti H2).
         apply IHmulti. split; easy.
Qed.

(* Compute beta (App (NVal 5) (BVal false)). *)
