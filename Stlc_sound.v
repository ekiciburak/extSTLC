From SFL Require Import Imports Auxiliaries Terms Typecheck Eval Progress Preservation.
Require Import Coq.Strings.String.



Definition stuck (t: term) := beta t = None /\ isvalue t = false.

Theorem soundness: forall n t t' T, 
  typecheck nil t = Some T /\
  evaln t n  = Some t' -> 
  ~ stuck t'.
Proof. unfold stuck, not.
       intro n.
       induction n as [| m IHn]; intros t t' T (Ha, Hb) (Hne, Hnv).
       - cbn in Hb. inversion Hb. rewrite <- H0 in *.
         specialize (progress t T Ha); intros Hp. (* Theorem 3.1 *)
         destruct Hp as [ Hp | Hp].
         + rewrite Hp in Hnv. contradict Hnv; easy.
         + destruct Hp as (t'', Hp).
           rewrite Hp in Hne. contradict Hne; easy.
       - cbn in Hb.
         specialize (progress t T Ha); intros Hp. (* Theorem 3.1 *)
         destruct Hp as [ Hp | Hp].
         + apply isvalue_beta in Hp.
           rewrite Hp in Hb. contradict Hb; easy.
         + destruct Hp as (e, He).
           rewrite He in Hb.
           specialize (preservation t e T (conj Ha He)); intros Hte. (* Theorem 3.2 *)
           specialize (IHn e t' T (conj Hte Hb)).
           apply IHn. split; easy.
Qed.

Theorem soundness_None: forall n t T, 
  typecheck nil t = Some T /\
  evaln t n = None -> 
  ~ stuck t.
Proof. intros n. unfold stuck.
       induction n; intros t T (H, H0).
       - unfold not. intros (Hnf, Hnv).
         specialize (progress t T H); intros.
         cbn in *. inversion H0.
       - unfold not. intros (Hnf, Hnv).
         specialize (progress t T H); intros.
         destruct H1. rewrite H1 in Hnv. easy.
         destruct H1. rewrite H1 in Hnf. easy.
Qed.