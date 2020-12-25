From SFL Require Import Imports Terms Auxiliaries Typecheck Eval.
Require Import Coq.Strings.String.


Lemma progress: forall t T,
  typecheck nil t  = Some T ->
  (isvalue t = true) \/ (exists t', beta t = Some t').
Proof. intros t.
       induction t; intros T Htc.
       - right. cbn in *. easy.
       - cbn. now left.
       - right.
         apply istypechecked_app in Htc.
         destruct Htc as (U, (Ha, Hb)).
         specialize (isvalue_dec t1); intros it1.
         destruct it1 as [it1 | it1]. 
         + specialize (isvalue_dec t2) as [it2 | it2].
           ++ case_eq t1.
              * intros x Ht1. subst. easy.
              * intros x tx e.
                cbn. rewrite it2. exists (subst e x t2).
                easy.
              * intros. subst. cbn in *. easy.
              * intros n Ht1. rewrite Ht1 in Ha.
                contradict Ha; easy.
              * intros n Ht1. rewrite Ht1 in Ha.
                contradict Ha; easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
           ++ specialize (IHt2 _ Hb).
              destruct IHt2 as [it2' | Hstep].
              +++ rewrite it2 in it2'. easy.
              +++ destruct Hstep as (t2', Hstep).
                  case_eq t1.
                  * intros. subst. easy.
                  * cbn. intros x tx e Ht1. rewrite it2.
                    rewrite Hstep.
                    exists (App (Lambda x tx e) t2'). easy.
                 * intros. subst. cbn in *. easy.
                 * intros n Ht1. rewrite Ht1 in Ha.
                   contradict Ha; easy.
                 * intros b Ht1. rewrite Ht1 in Ha.
                   contradict Ha; easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
         + specialize (IHt1 _ Ha).
           destruct IHt1 as [IHt1 | IHt1].
           ++ rewrite it1 in IHt1. contradict IHt1; easy.
           ++ destruct IHt1 as (t1', Hstep). cbn.
              rewrite it1. 
              rewrite Hstep.
              case_eq t1; try (intros; exists (App t1' t2); easy).
              intros x tx e Ht1.
              rewrite Ht1 in it1. easy.
       - cbn. now left.
       - cbn. now left.
       - right.
         apply istypechecked_ite in Htc.
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
         specialize (IHt3 _ Hc).
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
               * exists t2. easy.
               * exists t3. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
           ++ intros. subst. cbn in *. easy.
         + destruct Hstep as (t1', Hstep).
           cbn.
           rewrite Hstep.
           case_eq t1; intros; try (exists (ITE t1' t2 t3); easy).
           rewrite H in Hstep. easy.
       - apply istypechecked_fix in Htc.
         specialize (IHt _ Htc).
         destruct IHt as [ IHt | IHt ].
         + cbn. right.
           pose proof IHt as HH.
           apply isvalue_beta in IHt.
           rewrite IHt.
           case_eq t.
           ++ intros. subst. easy.
           ++ intros x tx e Ht.
              exists (subst e x (Fix (Lambda x tx e))). easy.
           ++ intros. subst. easy.
           ++ intros n Ht; rewrite Ht in Htc;
              contradict Htc; easy.
           ++ intros b Ht; rewrite Ht in Htc;
              contradict Htc; easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
           ++ intros. subst. easy.
         + destruct IHt as (t', IHt).
           right. cbn.
           rewrite IHt.
           case_eq t; try (exists (Fix t'); easy).
           * intros. rewrite H in IHt. easy.
       - specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_plus in Htc.
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
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
                     exists (NVal (m + n)). easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Plus (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Plus t1' t2); easy).
           intros n H0.
           subst. easy.
       - specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_minus in Htc.
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
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
                     exists (NVal (m - n)). easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Minus (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Minus t1' t2); easy).
           intros n H0.
           subst. easy.
       - specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_mult in Htc.
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
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
                     exists (NVal (m * n)). easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Mult (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Mult t1' t2); easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_eq in Htc0.
         destruct Htc0 as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
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
                     exists (BVal (Nat.eqb m n)). easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Eq (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Eq t1' t2); easy).
           intros n H0.
           subst. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         right.
         apply istypechecked_gt in Htc0.
         destruct Htc0 as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
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
                     ** exists (BVal false). easy.
                     ** exists  (BVal (Nat.leb n m)). easy.
                   * intros b Ht2 n Ht1.
                     rewrite Ht2 in Hb.
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Gt (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1].
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Gt t1' t2); easy).
           intros n H0.
           subst. easy.
Qed.

