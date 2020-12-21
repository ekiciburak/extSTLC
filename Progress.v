From SFL Require Import Imports Terms Auxiliaries Typecheck Eval.
Require Import Coq.Strings.String.

Lemma progressPre: forall t,
  istypechecked nil t  = true ->
  (isvalue t = true) \/ (exists t', term_eqbO (beta t) (Some t') = true).
Proof. intros t Htc.
       induction t; intros.
       - right. cbn in *. easy.
       - cbn. now left.
       - right.
         specialize (isvalue_dec t1); intros it1.
         destruct it1 as [it1 | it1].
         + specialize (isvalue_dec t2) as [it2 | it2].
           ++ case_eq t1.
              * intros x Ht1. subst. easy.
              * intros x tx e.
                cbn. rewrite it2. exists (subst e x t2).
                now rewrite term_eqbO_refl.
              * intros. subst. cbn in *. easy.
              * intros n Ht1. rewrite Ht1 in Htc.
                contradict Htc; easy.
              * intros n Ht1. rewrite Ht1 in Htc.
                contradict Htc; easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
           ++ assert (Htt2: istypechecked nil t2 = true).
              { apply istypechecked_t2 in Htc. easy. }
              specialize (IHt2 Htt2).
              destruct IHt2 as [it2' | Hstep].
              +++ rewrite it2 in it2'. easy.
              +++ destruct Hstep as (t2', Hstep).
                  case_eq t1.
                  * intros. subst. easy.
                  * cbn. intros x tx e Ht1. rewrite it2.
                    apply term_eqbO_eq in Hstep.
                    rewrite Hstep.
                    exists (App (Lambda x tx e) t2').
                    now rewrite term_eqbO_refl.
                 * intros. subst. cbn in *. easy.
                 * intros n Ht1. rewrite Ht1 in Htc.
                   contradict Htc; easy.
                 * intros b Ht1. rewrite Ht1 in Htc.
                   contradict Htc; easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
         + assert (Htt1: istypechecked nil t1 = true).
           { apply istypechecked_t1 in Htc. easy. }
           specialize (IHt1 Htt1).
           destruct IHt1 as [IHt1 | IHt1].
           ++ rewrite it1 in IHt1. contradict IHt1; easy.
           ++ destruct IHt1 as (t1', Hstep). cbn.
              rewrite it1. 
              apply term_eqbO_eq in Hstep.
              rewrite Hstep.
              case_eq t1; try (intros; exists (App t1' t2); rewrite term_eqbO_refl; easy).
              intros x tx e Ht1.
              rewrite Ht1 in it1. easy.
       - cbn. now left.
       - cbn. now left.
       - right.
         unfold istypechecked in Htc.
         case_eq (typecheck nil (ITE t1 t2 t3)). intros t Htca.
         apply istypechecked_ite2 in Htca.
         destruct Htca as (Ha, (Hb, Hc)).
         unfold istypechecked in IHt1, IHt2, IHt3.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         rewrite Hc in IHt3.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         specialize (IHt3 eq_refl).
         destruct IHt1 as [t1'| Hstep].
         + case_eq t1.
           ++ intros. subst. easy.
           ++ intros x tx e Ht1.
              rewrite Ht1 in Ha. contradict Ha. cbn.
              case_eq (typecheck (extend nil x tx) e); easy.
           ++ intros. subst. easy.
           ++ intros. rewrite H in Ha. contradict Ha; easy.
           ++ intros. cbn. 
              case_eq b; intros.
               * exists t2. rewrite term_eqbO_refl. easy.
               * exists t3. rewrite term_eqbO_refl. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
         + destruct Hstep as (t1', Hstep).
           apply term_eqbO_eq in Hstep. cbn.
           rewrite Hstep.
           case_eq t1; intros; try (exists (ITE t1' t2 t3); rewrite term_eqbO_refl; easy).
           rewrite H in Hstep. easy.
         + intros. rewrite H in Htc. easy.
       - pose proof Htc as Htc0.
         apply istypechecked_st in Htc.
         specialize (IHt Htc).
         destruct IHt as [ IHt | IHt ].
         + cbn. right.
           pose proof IHt as HH.
           apply isvalue_beta in IHt.
           rewrite IHt.
           case_eq t.
           ++ intros. subst. easy.
           ++ intros x tx e Ht.
              exists (subst e x (Fix (Lambda x tx e))).
              rewrite term_eqbO_refl. easy.
           ++ intros. subst. easy.
           ++ intros n Ht; rewrite Ht in Htc0;
              contradict Htc0; easy.
           ++ intros b Ht; rewrite Ht in Htc0;
              contradict Htc0; easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
         + destruct IHt as (t', IHt).
           right. cbn.
           apply term_eqbO_eq in IHt.
           rewrite IHt.
           case_eq t; try (exists (Fix t'); rewrite term_eqbO_refl; easy).
           * intros. rewrite H in IHt. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_plus2 in Htc0.
         destruct Htc0 as (Ha, Hb).
         unfold istypechecked in IHt1, IHt2.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         cbn.
         destruct it1 as [it1 | it1].
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     exists (NVal (m + n)).
                     rewrite term_eqbO_refl. easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   apply term_eqbO_eq in Hstep.
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Plus (NVal n) t2'); rewrite term_eqbO_refl; easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           apply term_eqbO_eq in Hstep.
           rewrite Hstep, it1.
           case_eq t1; try (exists (Plus t1' t2); rewrite term_eqbO_refl; easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_plus2 in Htc0.
         destruct Htc0 as (Ha, Hb).
         unfold istypechecked in IHt1, IHt2.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         cbn.
         destruct it1 as [it1 | it1].
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     exists (NVal (m - n)).
                     rewrite term_eqbO_refl. easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   apply term_eqbO_eq in Hstep.
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Minus (NVal n) t2'); rewrite term_eqbO_refl; easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           apply term_eqbO_eq in Hstep.
           rewrite Hstep, it1.
           case_eq t1; try (exists (Minus t1' t2); rewrite term_eqbO_refl; easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_plus2 in Htc0.
         destruct Htc0 as (Ha, Hb).
         unfold istypechecked in IHt1, IHt2.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         cbn.
         destruct it1 as [it1 | it1].
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     exists (NVal (m * n)).
                     rewrite term_eqbO_refl. easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   apply term_eqbO_eq in Hstep.
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Mult (NVal n) t2'); rewrite term_eqbO_refl; easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           apply term_eqbO_eq in Hstep.
           rewrite Hstep, it1.
           case_eq t1; try (exists (Mult t1' t2); rewrite term_eqbO_refl; easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_eq2 in Htc0.
         destruct Htc0 as (Ha, Hb).
         unfold istypechecked in IHt1, IHt2.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         cbn.
         destruct it1 as [it1 | it1].
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     exists (BVal (Nat.eqb m n)).
                     rewrite term_eqbO_refl. easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   apply term_eqbO_eq in Hstep.
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Eq (NVal n) t2'); rewrite term_eqbO_refl; easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           apply term_eqbO_eq in Hstep.
           rewrite Hstep, it1.
           case_eq t1; try (exists (Eq t1' t2); rewrite term_eqbO_refl; easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_eq2 in Htc0.
         destruct Htc0 as (Ha, Hb).
         unfold istypechecked in IHt1, IHt2.
         rewrite Ha in IHt1.
         rewrite Hb in IHt2.
         specialize (IHt1 eq_refl).
         specialize (IHt2 eq_refl).
         cbn.
         destruct it1 as [it1 | it1].
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     destruct m.
                     ** exists (BVal false).
                        rewrite term_eqbO_refl. easy.
                     ** exists  (BVal (Nat.leb n m)).
                        rewrite term_eqbO_refl. easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   apply term_eqbO_eq in Hstep.
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Gt (NVal n) t2'); rewrite term_eqbO_refl; easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           apply term_eqbO_eq in Hstep.
           rewrite Hstep, it1.
           case_eq t1; try (exists (Gt t1' t2); rewrite term_eqbO_refl; easy).
           intros n H0.
           subst. easy.
Qed.


Lemma progress: forall t T,
  typecheck nil t  = Some T ->
  (isvalue t = true) \/ (exists t', beta t = Some t').
Proof. intros t T Htc.
       specialize (progressPre t); intros.
       unfold istypechecked in *.
       rewrite Htc in H.
       specialize (H eq_refl).
       destruct H as [H| H].
       - now left.
       - destruct H as (t', Ht').
         right. exists t'.
         apply term_eqbO_eq in Ht'. 
         easy.
Qed.
