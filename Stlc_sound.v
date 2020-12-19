From SFL Require Import Imports Auxiliaries Terms Typecheck Eval Progress Preservation.
Require Import Coq.Strings.String.


Lemma preservation: forall (t t': term) (T: type),
   typecheck nil t = Some T ->
   beta t = Some t' ->
   typecheck nil t' = Some T.
Proof with eauto.
       intro t.
       induction t; intros.
       - cbn in *. easy.
       - cbn in H0. easy.
       - cbn in H0.
         case_eq t1.
         + intros x Ht1;
           rewrite Ht1 in H;
           contradict H; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in H0.
           case_eq (isvalue t2); intros.
           ++ rewrite H1 in H0.
              inversion H0.
              case_eq t2.
              +++ intros s Hts.
                  rewrite Hts in H1. easy.
              +++ intros x' tx' e' Ht2.
                  cbn in H.
                  rewrite Ht1, Ht2 in H.
                  cbn in H.
                  case_eq (typecheck (extend nil x tx) e); intros.
                  * rewrite H2 in H.
                    case_eq (typecheck (extend nil x' tx') e'); intros.
                    ** rewrite H4 in H.
                       case_eq (type_eqb tx (Arrow tx' t0)); intros.
                       *** rewrite H5 in H.
                           specialize (subst_preserves_typing x e 
                                 (Lambda x' tx' e') t tx nil); intros.
                           rewrite H6.
                           ++++ easy.
                           ++++ easy.
                           ++++ cbn. rewrite H4.
                                apply type_eqb_eq in H5.
                                rewrite H5. easy.
                       *** rewrite H5 in H; contradict H; easy.
                    ** rewrite H4 in H; contradict H; easy.
                  * rewrite H2 in H; contradict H; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros n Ht2.
                  rewrite Ht1, Ht2 in H.
                  cbn in H.
                  case_eq ( typecheck (extend nil x tx) e); intros.
                  * rewrite H2 in H.
                    case_eq (type_eqb tx Int); intros.
                    ** rewrite H4 in H.
                       specialize (subst_preserves_typing x e 
                                      (NVal n) t tx nil); intros.
                       rewrite H5.
                       *** easy.
                       *** easy.
                       *** cbn. 
                           apply type_eqb_eq in H4. rewrite H4. easy.
                    ** rewrite H4 in H; contradict H; easy.
                  * rewrite H2 in H; contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht1, Ht2 in H.
                  cbn in H.
                  case_eq ( typecheck (extend nil x tx) e); intros.
                  * rewrite H2 in H.
                    case_eq (type_eqb tx Bool); intros.
                    ** rewrite H4 in H.
                       specialize (subst_preserves_typing x e 
                                      (BVal b) t tx nil); intros.
                       rewrite H5.
                       *** easy.
                       *** easy.
                       *** cbn. 
                           apply type_eqb_eq in H4. rewrite H4. easy.
                    ** rewrite H4 in H; contradict H; easy.
                  * rewrite H2 in H; contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros t2' Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H1.
                  contradict H1; easy.
           ++ rewrite H1 in H0.
              case_eq (beta t2). intros t2' Ht2.
              +++ rewrite Ht2 in H0.
                  inversion H0. cbn.
                  rewrite Ht1 in H.
                  cbn in H.
                  case_eq (typecheck (extend nil x tx) e); intros.
                  ++++ rewrite H2 in H.
                       case_eq (typecheck nil t2); intros.
                       * rewrite H4 in H.
                         case_eq (type_eqb tx t0); intros.
                         ** rewrite H5 in H.
                            specialize (IHt2 t2' t0 H4 Ht2).
                            rewrite IHt2. rewrite H5. easy.
                         ** rewrite H5 in H. contradict H; easy.
                       * rewrite H4 in H. contradict H; easy.
                  ++++ rewrite H2 in H. contradict H; easy.
               +++ intro Ht2. rewrite Ht2 in H0.
                   contradict H0; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           rewrite H1 in H0.
           specialize (AppAppE t1 t2 T H); intros.
           destruct H2 as (U, H2).
           specialize (progress t1 (Arrow U T) H2); intros.
           destruct H3 as [ H3 | H3].
           ++ rewrite Ht1 in H3. rewrite H3 in H1. contradict H1; easy.
           ++ destruct H3 as (t1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H1.
              specialize (AppApp_TL2 t1 t2 t1' H1 H3); intros.
              specialize (AppAppT t1 t2 T U H H2); intros.
              cbn.
              specialize (IHt1 t1' (Arrow U T) H2 H3).
              rewrite IHt1, H6, type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in H.
           cbn in H. inversion H; easy.
         + intros n Ht1.
           rewrite Ht1 in H.
           cbn in H. inversion H; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           rewrite H1 in H0.
           specialize (AppAppE t1 t2 T H); intros.
           destruct H2 as (U, H2).
           specialize (progress t1 (Arrow U T) H2); intros.
           destruct H3 as [ H3 | H3].
           ++ rewrite Ht1 in H3. rewrite H3 in H1. contradict H1; easy.
           ++ destruct H3 as (e1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H1.
              specialize (AppApp_TL2 t1 t2 e1' H1 H3); intros.
              specialize (AppAppT t1 t2 T U H H2); intros.
              cbn.
              specialize (IHt1 e1' (Arrow U T) H2 H3).
              rewrite IHt1, H6, type_eqb_refl. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           rewrite H1 in H0.
           specialize (AppAppE t1 t2 T H); intros.
           destruct H2 as (U, H2).
           specialize (progress t1 (Arrow U T) H2); intros.
           destruct H3 as [ H3 | H3].
           ++ rewrite Ht1 in H3. rewrite H3 in H1. contradict H1; easy.
           ++ destruct H3 as (t1', H3).
              rewrite <- Ht1 in H0.
              rewrite H3 in H0.
              inversion H0.
              rewrite <- Ht1 in H1.
              specialize (AppApp_TL2 t1 t2 t1' H1 H3); intros.
              specialize (AppAppT t1 t2 T U H H2); intros.
              cbn.
              specialize (IHt1 t1' (Arrow U T) H2 H3).
              rewrite IHt1, H6, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H1 in H.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H2 in H. destruct t; easy.
              +++ rewrite H2 in H. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H1 in H.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H2 in H. destruct t; easy.
              +++ rewrite H2 in H. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H1 in H.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H2 in H. destruct t; easy.
              +++ rewrite H2 in H. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H1 in H.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H2 in H. destruct t; easy.
              +++ rewrite H2 in H. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck nil e1); intros.
           ++ rewrite H1 in H.
              destruct t.
              case_eq (typecheck nil e2); intros.
              +++ rewrite H2 in H. destruct t; easy.
              +++ rewrite H2 in H. contradict H0. easy.
              +++ contradict H. easy.
              +++ contradict H. easy.
           ++ rewrite H1 in H. contradict H; easy.
       - cbn in H0. easy.
       - cbn in H0. easy.
       - cbn in H0.
         pose proof H as HH.
         apply istypechecked_ite2 in H.
         destruct H as (Ha, (Hb, Hc)).
         case_eq t1.
         + intros. rewrite H in Ha. contradict Ha; easy.
         + intros x tx e Ht1. rewrite Ht1 in Ha. cbn in Ha.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H in Ha. contradict Ha; easy.
           ++ rewrite H in Ha. contradict Ha; easy.
         + intros e1 e2 Ht1. rewrite Ht1 in H0.
           assert (isvalue (ITE t1 t2 t3) = false) by easy.
           rewrite Ht1 in Ha.
           specialize (AppAppE e1 e2 Bool Ha); intros.
           destruct H1 as (U, H1).
           specialize (progress (App e1 e2) Bool Ha ); intros.
           destruct H2 as [H2 | H2].
           ++ cbn in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite H2 in H0.
              inversion H0.
              rewrite <- Ht1 in Ha, H2.
              specialize (IHt1 e1' Bool Ha H2).
              cbn.
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in Ha. contradict Ha; easy.
         + intros b Ht1.
           rewrite Ht1 in H0.
           case_eq b; intros.
           ++ rewrite H in H0.
              inversion H0. rewrite <- H2. easy.
           ++ rewrite H in H0.
              inversion H0. rewrite <- H2. easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           specialize (progress t1 Bool Ha); intros.
           destruct H1 as [H1 | H1].
           ++ rewrite Ht1 in H1. rewrite H1 in H.
              contradict H; easy.
           ++ destruct H1 as (e1', H1).
              rewrite Ht1 in H1.
              rewrite H1 in H0.
              inversion H0. cbn.
              rewrite <- Ht1 in H1.
              specialize (IHt1 e1' Bool Ha H1).
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
              specialize (IHt1 f' Bool Ha H1).
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
              specialize (IHt1 t1' Bool Ha H1).
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
              specialize (IHt1 t1' Bool Ha H1).
              rewrite IHt1, Hb, Hc.
              rewrite !type_eqb_refl. easy.
       - cbn in H0.
         case_eq t.
         + intros. rewrite H1 in H. contradict H; easy.
         + intros x tx e Ht1.
           rewrite Ht1 in H0. inversion H0.
           rewrite Ht1 in H.
           cbn in H.
           case_eq (typecheck (extend nil x tx) e); intros.
           ++ rewrite H1 in H.
              case_eq (type_eqb tx t0); intros.
              +++ rewrite H3 in H.
                  specialize (subst_preserves_typing x e (Fix (Lambda x tx e)) T T nil); intros.
                  rewrite H4. easy.
                  apply type_eqb_eq in H3.
                  inversion H. subst. easy.
                  cbn. rewrite H1, H3. easy.
              +++ rewrite H3 in H. contradict H; easy.
           ++ rewrite H1 in H. contradict H; easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (App e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros n Ht1.
           rewrite Ht1 in H. cbn in H. contradict H; easy.
         + intros b Ht1.
           rewrite Ht1 in H. cbn in H. contradict H; easy.
         + intros e1 e2 e3 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (ITE e1 e2 e3) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Fix e1) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Plus e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Minus e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Mult e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Eq e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
         + intros e1 e2 Ht1.
           rewrite Ht1 in H0.
           assert (isvalue (Gt e1 e2) = false) by easy.
           apply fixTyping in H.
           specialize (progress t (Arrow T T) H); intros.
           destruct H2 as [ H2 | H2].
           ++ rewrite Ht1 in H2. rewrite H1 in H2. contradict H2; easy.
           ++ destruct H2 as (e1', H2).
              rewrite Ht1 in H2.
              rewrite H2 in H0.
              inversion H0.
              cbn.
              rewrite <- Ht1 in H2.
              specialize (IHt e1' (Arrow T T) H H2).
              rewrite IHt, type_eqb_refl. easy.
       - apply istypechecked_plus3 in H.
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
              specialize (IHt1 t1' Int Ha H1).
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
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_plus3 in H.
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
              specialize (IHt1 t1' Int Ha H1).
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
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_plus3 in H.
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
              specialize (IHt1 t1' Int Ha H1).
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
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_eq3 in H.
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
              specialize (IHt1 t1' Int Ha H1).
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
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
              rewrite IHt1, Hb, Hc. easy.
       - apply istypechecked_eq3 in H.
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
              specialize (IHt1 t1' Int Ha H1).
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
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros m Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros b Ht2.
                  rewrite Ht2 in H. contradict H; easy.
              +++ intros e1 e2 e3 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
                  rewrite IHt2, Hc. easy.
              +++ intros e1 e2 Ht2.
                  rewrite Ht2 in H0.
                  inversion H0.
                  cbn.
                  specialize (IHt2 t2' Int Hb H).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
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
              specialize (IHt1 t1' Int Ha H1).
              rewrite IHt1, Hb, Hc. easy.
Qed.

Lemma preservationE: forall (t t': term),
   beta t = Some t' ->
   (exists T, typecheck nil t = Some T) ->
    exists K, typecheck nil t' = Some K.
Proof. intros.
       destruct H0. exists x.
       specialize (preservation t t' x H0 H); intros. easy.
Qed.



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

Check progress.

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

Compute beta (App (NVal 5) (BVal false)).
