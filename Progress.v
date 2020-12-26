From SFL Require Import Imports Terms Auxiliaries Typecheck Eval.
Require Import Coq.Strings.String.


Lemma progress: forall t T,
  typecheck nil t  = Some T ->
  (isvalue t = true) \/ (exists t', beta t = Some t').
Proof. intros t.
       induction t; intros T Htc.
       - right. cbn in *. easy.
       - cbn. now left.
       - right. (* 1 *)
         apply istypechecked_app in Htc. (* Lemma 3.1 *)
         destruct Htc as (U, (Ha, Hb)).
         specialize (isvalue_dec t1); intros it1. (* 1-a *)
         destruct it1 as [it1 | it1]. 
         + specialize (isvalue_dec t2) as [it2 | it2]. (* 1-a-i *)
           ++ case_eq t1.
              * intros x Ht1. subst. easy.
              * intros x tx e.
                cbn. rewrite it2. exists (subst e x t2). (* 1-a-i-bullet_1 *)
                easy.
              * intros. subst. cbn in *. easy.
              * intros n Ht1. rewrite Ht1 in Ha.
                contradict Ha; easy.  (* 1-a-i-bullet_2 *)
              * intros n Ht1. rewrite Ht1 in Ha.
                contradict Ha; easy.  (* 1-a-i-bullet_3 *)
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
              * intros. subst. cbn in *. easy.
           ++ specialize (IHt2 _ Hb). (* 1-a-ii *)
              destruct IHt2 as [it2' | Hstep].
              +++ rewrite it2 in it2'. easy. (* 1-a-ii-A *)
              +++ destruct Hstep as (t2', Hstep).
                  case_eq t1.  (* 1-a-ii-B *)
                  * intros. subst. easy.
                  * cbn. intros x tx e Ht1. rewrite it2.
                    rewrite Hstep.
                    exists (App (Lambda x tx e) t2'). easy. (* 1-a-ii-B-bullet_1 *)
                 * intros. subst. cbn in *. easy.
                 * intros n Ht1. rewrite Ht1 in Ha.
                   contradict Ha; easy.  (* 1-a-ii-B-bullet_2 *)
                 * intros b Ht1. rewrite Ht1 in Ha.
                   contradict Ha; easy.  (* 1-a-ii-B-bullet_3 *)
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
                 * intros. subst. cbn in *. easy.
         + specialize (IHt1 _ Ha). (* 1-b *)
           destruct IHt1 as [IHt1 | IHt1].
           ++ rewrite it1 in IHt1. contradict IHt1; easy. (* 1-b-i *)
           ++ destruct IHt1 as (t1', Hstep). cbn.
              rewrite it1. 
              rewrite Hstep.
              case_eq t1; try (intros; exists (App t1' t2); easy). (* 1-b-ii-bullet *)
              intros x tx e Ht1.
              rewrite Ht1 in it1. easy.
       - cbn. now left.
       - cbn. now left.
       - right. (* 2 *)
         apply istypechecked_ite in Htc. (* Lemma 3.2 *)
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
         specialize (IHt3 _ Hc).
         destruct IHt1 as [t1'| Hstep]. (* 2-a *)
         + case_eq t1.
           ++ intros. subst. easy.
           ++ intros x tx e Ht1. (* 2-a-bullet_1 *)
              rewrite Ht1 in Ha. contradict Ha. cbn.
              case_eq (typecheck (extend nil x tx) e); easy.
           ++ intros. subst. easy.
           ++ intros. rewrite H in Ha. contradict Ha; easy. (* 2-a-bullet_2 *)
           ++ intros. cbn. (* 2-a-bullet_3 *)
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
         + destruct Hstep as (t1', Hstep). (* 2-b *)
           cbn.
           rewrite Hstep.
           case_eq t1; intros; try (exists (ITE t1' t2 t3); easy).
           rewrite H in Hstep. easy.
       - apply istypechecked_fix in Htc. (* 3 *) (* Lemma 3.3 *)
         specialize (IHt _ Htc).
         destruct IHt as [ IHt | IHt ].
         + cbn. right. (* 3-a *)
           pose proof IHt as HH.
           apply isvalue_beta in IHt.
           rewrite IHt.
           case_eq t.
           ++ intros. subst. easy.
           ++ intros x tx e Ht.
              exists (subst e x (Fix (Lambda x tx e))). easy. (* 3-a-bullet_1 *)
           ++ intros. subst. easy.
           ++ intros n Ht; rewrite Ht in Htc; (* 3-a-bullet_2 *)
              contradict Htc; easy.
           ++ intros b Ht; rewrite Ht in Htc; (* 3-a-bullet_3 *)
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
           case_eq t; try (exists (Fix t'); easy). (* 3-b *)
           * intros. rewrite H in IHt. easy.
       - specialize (isvalue_dec t1); intros it1. (* 4 *)
         right.
         apply istypechecked_plus in Htc.  (* Lemma 3.4 *)
         destruct Htc as (Ha, (Hb, Hc)).
         specialize (IHt1 _ Ha).
         specialize (IHt2 _ Hb).
         cbn.
         destruct it1 as [it1 | it1].  (* 4-a *)
         + case_eq t1; try (intros; rewrite H in it1; cbn in it1; easy).
            ++ intros x tx e Ht1.  (* 4-a-i *)
               rewrite Ht1 in Ha. cbn in Ha.
               case_eq (typecheck (extend nil x tx) e); intros;
               rewrite H in Ha; contradict Ha; easy.
            ++ destruct IHt2 as [IHt2 | IHt2].  (* 4-a-ii-A *)
               +++ case_eq t2; try (intros; rewrite H in IHt2; cbn in IHt2; easy).
                   * intros x tx e Ht2.  (* 4-a-ii-A-bullet_1 *)
                     rewrite Ht2 in Hb. cbn in Hb.
                     case_eq (typecheck (extend nil x tx) e); intros;
                     rewrite H in Hb; contradict Hb; easy.
                   * intros n Ht2 m Ht1.
                     exists (NVal (m + n)). easy.
                   * intros b Ht2 n Ht1.  (* 4-a-ii-A-bullet_2 *)
                     rewrite Ht2 in Hb.   (* 4-a-ii-A-bullet_3 *)
                     contradict Hb; easy.
               +++ destruct IHt2 as (t2', Hstep).  (* 4-a-ii-B *)
                   rewrite Hstep. cbn. intros n Ht1.
                   case_eq t2; try (exists (Plus (NVal n) t2'); easy).
                   intros m H1.
                   rewrite H1 in Hstep. cbn in Hstep.
                   contradict Hstep; easy.
            ++ cbn. intros b Ht1. rewrite Ht1 in Ha.  (* 4-a-iii *)
               contradict Ha; easy.
         + destruct IHt1 as [IHt1 | IHt1]. (* 4-b *)
           rewrite it1 in IHt1. easy.
           destruct IHt1 as (t1', Hstep).
           rewrite Hstep, it1.
           case_eq t1; try (exists (Plus t1' t2); easy).
           intros n H0.
           subst. easy.
       - specialize (isvalue_dec t1); intros it1.  (* 5 *)
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

