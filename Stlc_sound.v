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


Definition stuck_b (e: term) :=
  beta e = None /\ isvalue e = false.

Theorem soundness: forall t t' T, 
  typecheck nil t = Some T -> 
  multistep t t' -> 
  ~ stuck t'.
Proof. intros. unfold stuck.
       induction H0; intros.
       - unfold not. intros (Hnf, Hnv).
         unfold normal_form in *. apply Hnf.
         unfold step.
         specialize (progress x T H); intros.
         destruct H0. rewrite Hnv in H0. easy.
         destruct H0. exists x0. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (preservation x y T H H0); intros.
         specialize (IHmulti H2).
         apply IHmulti. split; easy.
Qed.

Theorem soundness_R: forall n t t' T, 
  typecheck nil t = Some T -> 
  evaln t n  = Some t' -> 
  ~ stuck_b t'.
Proof. intros n. unfold stuck_b.
       induction n; intros.
       - unfold not. intros (Hnf, Hnv).
         specialize (progress t T H); intros.
         cbn in *. inversion H0. subst.
         destruct H1. rewrite H1 in Hnv. easy.
         destruct H1 as (t, Ha).
         rewrite Ha in Hnf. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         cbn in H0, IHn.
         case_eq (beta t); intros.
         rewrite H1 in H0.
         specialize (preservation t t0 T H H1); intros.
         specialize (IHn t0 t' T H2 H0).
         apply IHn. split; easy.
         rewrite H1 in H0. easy.
Qed.

Theorem soundness_Q: forall n t T, 
  typecheck nil t = Some T -> 
  evaln t n  = None -> 
  ~ stuck_b t.
Proof. intros n. unfold stuck_b.
       induction n; intros.
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
  typecheck nil t = Some T -> 
  multistep t t' -> 
  ~ stuck_b t'.
Proof. intros. unfold stuck_b.
       induction H0; intros.
       - unfold not. intros (Hnf, Hnv).
         specialize (progress x T H); intros.
         destruct H0. rewrite H0 in Hnv. easy.
         destruct H0 as (t, Ha).
         rewrite Ha in Hnf. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (preservation x y T H H0); intros.
         specialize (IHmulti H2).
         apply IHmulti. split; easy.
Qed.

(* Compute beta (App (NVal 5) (BVal false)). *)
