From SFL Require Import Imports Terms Auxiliaries Typecheck Eval Progress.
Require Import Coq.Strings.String.


Lemma preservation: forall (t t': term) (T: type),
   typecheck nil t = Some T /\
   beta t = Some t' ->
   typecheck nil t' = Some T.
Proof with eauto.
       intro t.
       induction t; intros t' T (H, H0).
       - cbn in *. easy.
       - cbn in H0. easy.
       - cbn in H0.  (* 1 *)
         apply istypechecked_app in H. (* Lemma 3.1 *)
         destruct H as (U, (H1, H2)).
         case_eq t1.
         + intros x Ht1;
           rewrite Ht1 in H0;
           contradict H0; easy.
         + intros x v e Ht1. (* 1-a: lambda x: v. e *)
           rewrite Ht1 in H0.
           case_eq (isvalue t2); intros.
           ++ rewrite H in H0. (* 1-a-i *)
              inversion H0.
              specialize (subst_preserves_typing e t2 x T U nil); intros. (* Lemma 3.5 *)
              rewrite H3.
              +++ easy.
              +++ rewrite Ht1 in H1. cbn in H1. (* 1-a-bullet_1 *)
                  case_eq (typecheck (extend nil x v) e); intros.
                  * rewrite H5 in H1.
                    inversion H1. subst. easy.
                  * rewrite H5 in H1. contradict H1; easy.
              +++ exact H2. (* 1-a-bullet_2 *)
           ++ rewrite H in H0. (* 1-a-ii *)
              specialize (progress t2 U H2); intros. (* Theorem 3.1 *)
              destruct H3 as [H3 | H3].
              +++ rewrite H in H3. contradict H3; easy.
              +++ destruct H3 as (t2', H3).
                  rewrite H3 in H0.
                  inversion H0. cbn.
                  rewrite Ht1 in H1.
                  cbn in H1. rewrite H1.
                  specialize (IHt2 t2' U (conj H2 H3)).
                  rewrite IHt2, type_eqb_refl. easy.
         + intros e1 e2 Ht1. (* 1-b: t1 = e1 e2 *)
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 (Arrow U T) H1); intros. (* Theorem 3.1 *)
           destruct H3 as [ H3 | H3 ].
           ++ rewrite Ht1 in H3. rewrite H in H3. contradict H3; easy.
           ++ destruct H3 as (t1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H. cbn.
              specialize (IHt1 t1' (Arrow U T) (conj H1 H3)).
              rewrite IHt1, H2, type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in H1.
           cbn in H1. inversion H1; easy.
         + intros n Ht1.
           rewrite Ht1 in H1.
           cbn in H1. inversion H1; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 (Arrow U T) H1); intros. (* Theorem 3.1 *)
           destruct H3 as [ H3 | H3 ].
           ++ rewrite Ht1 in H3. rewrite H in H3. contradict H3; easy.
           ++ destruct H3 as (e1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H. cbn.
              specialize (IHt1 e1' (Arrow U T) (conj H1 H3)).
              rewrite IHt1, H2, type_eqb_refl. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 (Arrow U T) H1); intros.
           destruct H3 as [ H3 | H3 ].
           ++ rewrite Ht1 in H3. rewrite H in H3. contradict H3; easy.
           ++ destruct H3 as (t1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H. cbn.
              specialize (IHt1 t1' (Arrow U T) (conj H1 H3)).
              rewrite IHt1, H2, type_eqb_refl. easy.
         + intros e1 e2 Ht1. (* 1-e: t1 = Plus e1 e2 *)
           rewrite Ht1 in H1.
           cbn in H1.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in H1.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H3 in H1. destruct t; contradict H1; easy.
              +++ rewrite H3 in H1. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H in H1. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H1.
           cbn in H1.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in H1.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H3 in H1. destruct t; contradict H1; easy.
              +++ rewrite H3 in H1. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H in H1. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H1.
           cbn in H1.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in H1.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H3 in H1. destruct t; contradict H1; easy.
              +++ rewrite H3 in H1. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H in H1. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H1.
           cbn in H1.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in H1.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H3 in H1. destruct t; contradict H1; easy.
              +++ rewrite H3 in H1. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H in H1. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H1.
           cbn in H1.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in H1.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H3 in H1. destruct t; contradict H1; easy.
              +++ rewrite H3 in H1. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H in H1. contradict H1; easy.
       - cbn in H0. easy.
       - cbn in H0. easy.
       - cbn in H0. (* 2 *)
         pose proof H as HH.
         apply istypechecked_ite in H. (* Lemma 3.2 *)
         destruct H as (Ha, (Hb, Hc)).
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1. rewrite Ht1 in Ha. cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1. rewrite Ht1 in H0. (* 2-b: t1 = e1 e2 *)
           assert (isvalue (ITE t1 t2 t3) = false) by easy.
           rewrite Ht1 in Ha.
           specialize (progress (App e1 e2) Bool Ha ); intros. (* Theorem 3.1 *)
           destruct H1 as [H1 | H1].
           ++ cbn in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in Ha, H1.
              specialize (IHt1 t1' Bool (conj Ha H1)).
              rewrite IHt1, Hb, Hc, !type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros b Ht1. (* 2-c: t1 = BVal b *)
           rewrite Ht1 in H0.
           case_eq b; intros.
           ++ rewrite H in H0.
              inversion H0. rewrite <- H2. easy. (* 2-c-bullet_1 *)
           ++ rewrite H in H0.
              inversion H0. rewrite <- H2. easy. (* 2-c-bullet_2 *)
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           specialize (progress t1 Bool Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H1 in H.
              contradict H; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1.
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in H1.
              specialize (IHt1 t1' Bool (conj Ha H1)).
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
         + intros f Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix f) = false) by easy.
           specialize (progress t1 Bool Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H1 in H.
              contradict H; easy.
           ++ destruct H1 as (f', H1).
              rewrite Ht1 in H1.
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in H1.
              specialize (IHt1 f' Bool (conj Ha H1)).
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in Ha.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H1 in Ha.
                  destruct t; contradict Ha; easy.
              +++ rewrite H1 in Ha. contradict Ha; easy.
              +++ contradict Ha; easy.
              +++ contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in Ha.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H1 in Ha.
                  destruct t; contradict Ha; easy.
              +++ rewrite H1 in Ha. contradict Ha; easy.
              +++ contradict Ha; easy.
              +++ contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H in Ha.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H1 in Ha.
                  destruct t; contradict Ha; easy.
              +++ rewrite H1 in Ha. contradict Ha; easy.
              +++ contradict Ha; easy.
              +++ contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           specialize (progress t1 Bool Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H1 in H.
              contradict H; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1.
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in H1.
              specialize (IHt1 t1' Bool (conj Ha H1)).
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           specialize (progress t1 Bool Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H1 in H.
              contradict H; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1.
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in H1.
              specialize (IHt1 t1' Bool (conj Ha H1)).
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
       - cbn in H0. (* 3 *)
         pose proof H as Ha.
         apply istypechecked_fix in H. (* Lemma 3.3 *)
         case_eq t.
         + intros. rewrite H1 in H. contradict H; easy.
         + intros x v e Ht1. (* 3-b: t1 = lambda x: v. e *)
           rewrite Ht1 in H0. inversion H0.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck (extend nil x v) e); intros.
           ++ rewrite H1 in H.
              specialize (subst_preserves_typing e (Fix (Lambda x v e)) x T T nil); intros. (* Lemma 3.5 *)
              rewrite H3.
              +++ easy.
              +++ inversion H. subst. easy.
              +++ rewrite Ht1 in Ha. easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (f', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt f' (Arrow T T) (conj H H2)).
              rewrite IHt, type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in H. cbn in H. contradict H; easy.
         + intros b Ht1.
           rewrite Ht1 in H. cbn in H. contradict H; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (f', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt f' (Arrow T T) (conj H H2)).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) (conj H H2)).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H. cbn in H.
           destruct (typecheck nil e1). destruct t0.
           destruct (typecheck nil e2). destruct t0.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H. cbn in H.
           destruct (typecheck nil e1). destruct t0.
           destruct (typecheck nil e2). destruct t0.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H. cbn in H.
           destruct (typecheck nil e1). destruct t0.
           destruct (typecheck nil e2). destruct t0.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H. cbn in H.
           destruct (typecheck nil e1). destruct t0.
           destruct (typecheck nil e2). destruct t0.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H. cbn in H.
           destruct (typecheck nil e1). destruct t0.
           destruct (typecheck nil e2). destruct t0.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
           contradict H; easy.
       - apply istypechecked_plus in H. (* 4 *) (* Lemma 3.4 *)
         destruct H as (Ha, (Hb, Hc)).
         cbn in H0.
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1. rewrite H1 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H1. 
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb. rewrite Hc. easy.
         + intros n Ht1. (* 4-c: t1 = NVal n *)
           rewrite Ht1 in H0. cbn in H0.
           specialize (progress t2 Int Hb); intros. (* Theorem 3.1 *)
           destruct H as [H | H].
           ++ apply isvalue_beta in H. (* 4-c-bullet_1 *)
              rewrite H in H0.
              case_eq t2; try (intros; rewrite H1 in H0; contradict H; easy).
              intros m Ht2.
              rewrite Ht2 in H0. inversion H0.
              cbn. subst. easy.
           ++ destruct H as (t2', H). (* 4-c-bullet_2 *)
              rewrite H in H0.
              case_eq t2.
              +++ intros. rewrite H1 in H. contradict H. easy.
              +++ intros x tx e Ht2.
                  rewrite Ht2 in H.
                  contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
         + intros b Ht1.
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_minus in H. (* 5 *)
         destruct H as (Ha, (Hb, Hc)).
         cbn in H0.
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1. rewrite H1 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H1. 
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb. rewrite Hc. easy.
         + intros n Ht1.
           rewrite Ht1 in H0. cbn in H0.
           specialize (progress t2 Int Hb); intros.
           destruct H as [H | H].
           ++ apply isvalue_beta in H.
              rewrite H in H0.
              case_eq t2; try (intros; rewrite H1 in H0; contradict H; easy).
              intros m Ht2.
              rewrite Ht2 in H0. inversion H0.
              cbn. subst. easy.
           ++ destruct H as (t2', H).
              rewrite H in H0.
              case_eq t2.
              +++ intros. rewrite H1 in H. contradict H. easy.
              +++ intros x tx e Ht2.
                  rewrite Ht2 in H.
                  contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
         + intros b Ht1. 
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_mult in H.
         destruct H as (Ha, (Hb, Hc)).
         cbn in H0.
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1. rewrite H1 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H1. 
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb. rewrite Hc. easy.
         + intros n Ht1.
           rewrite Ht1 in H0. cbn in H0.
           specialize (progress t2 Int Hb); intros.
           destruct H as [H | H].
           ++ apply isvalue_beta in H.
              rewrite H in H0.
              case_eq t2; try (intros; rewrite H1 in H0; contradict H; easy).
              intros m Ht2.
              rewrite Ht2 in H0. inversion H0.
              cbn. subst. easy.
           ++ destruct H as (t2', H).
              rewrite H in H0.
              case_eq t2.
              +++ intros. rewrite H1 in H. contradict H. easy.
              +++ intros x tx e Ht2.
                  rewrite Ht2 in H.
                  contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
         + intros b Ht1. 
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_eq in H.
         destruct H as (Ha, (Hb, Hc)).
         cbn in H0.
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1. rewrite H1 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H1. 
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb. rewrite Hc. easy.
         + intros n Ht1.
           rewrite Ht1 in H0. cbn in H0.
           specialize (progress t2 Int Hb); intros.
           destruct H as [H | H].
           ++ apply isvalue_beta in H.
              rewrite H in H0.
              case_eq t2; try (intros; rewrite H1 in H0; contradict H; easy).
              intros m Ht2.
              rewrite Ht2 in H0. inversion H0.
              cbn. subst. easy.
           ++ destruct H as (t2', H).
              rewrite H in H0.
              case_eq t2.
              +++ intros. rewrite H1 in H. contradict H. easy.
              +++ intros x tx e Ht2.
                  rewrite Ht2 in H.
                  contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
         + intros b Ht1. 
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_gt in H.
         destruct H as (Ha, (Hb, Hc)).
         cbn in H0.
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in Ha.
           cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite Ht1 in H1. rewrite H1 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H1. 
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb. rewrite Hc. easy.
         + intros n Ht1.
           rewrite Ht1 in H0. cbn in H0.
           specialize (progress t2 Int Hb); intros.
           destruct H as [H | H].
           ++ apply isvalue_beta in H.
              rewrite H in H0.
              case_eq t2; try (intros; rewrite H1 in H0; contradict H; easy).
              intros m Ht2.
              rewrite Ht2 in H0. inversion H0.
              cbn. subst. easy.
           ++ destruct H as (t2', H).
              rewrite H in H0.
              case_eq t2.
              +++ intros. rewrite H1 in H. contradict H. easy.
              +++ intros x tx e Ht2.
                  rewrite Ht2 in H.
                  contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int (conj Hb H)).
                  rewrite IHt2, Hc. easy.
         + intros b Ht1. 
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           rewrite H in H0.
           specialize (progress t1 Int Ha); intros.
           destruct H1 as [ H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H in H1. contradict H1; easy.
           ++ destruct H1 as (t1', H1).
              rewrite <- Ht1 in H0.
              rewrite H1 in H0.
              inversion H0.
              cbn.
              specialize (IHt1 t1' Int (conj Ha H1)).
              rewrite IHt1, Hb, Hc. easy.
Qed.


Lemma preservationE: forall (t t': term),
   beta t = Some t' ->
   (exists T, typecheck nil t = Some T) ->
    exists K, typecheck nil t' = Some K.
Proof. intros.
       destruct H0. exists x.
       specialize (preservation t t' x (conj H0 H)); intros. easy.
Qed.
