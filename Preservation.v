From SFL Require Import Imports Terms Auxiliaries Typecheck Eval Progress.
Require Import Coq.Strings.String.


Lemma free_in_context: forall t x T G,
   List.In x (fv t) ->
   typecheck G t = Some T ->
   exists T', lookup G x = Some T'.
Proof. intro t.
       induction t; intros.
       - cbn in *. destruct H. subst.
         exists T. easy. easy.
       - cbn in *. apply List.filter_In in H.
         destruct H.
         case_eq (typecheck (extend G s t) t0 ); intros.
         + rewrite H2 in H0. inversion H0.
           specialize (IHt x t1 (extend G s t) H H2).
           destruct IHt. exists x0. cbn in *.
           case_eq (s =? x); intros.
           ++ rewrite String.eqb_sym in H1.
              rewrite H5 in H1. easy.
           ++ rewrite H5 in H3. easy.
         + rewrite H2 in H0. easy.
       - cbn in *. apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq(typecheck G t2); intros.
           ++ destruct H.
              +++ specialize (IHt1 x t G H H1). easy.
              +++ specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0.
              rewrite H1 in H0.
              destruct t in H0; easy.
         + rewrite H1 in H0. easy.
       - cbn in H. easy.
       - cbn in H. easy.
       - cbn in H. apply listE in H.
         destruct H.
         cbn in H0.
         case_eq (typecheck G t1 ); intros.
         + apply IHt1 with (T := t). easy. easy.
         + rewrite H1 in H0. easy.
         + apply List.in_app_or in H.
           destruct H.
           ++ case_eq (typecheck G t2); intros.
              +++ apply IHt2 with (T := t). easy. easy.
              +++ cbn in H0. rewrite H1 in H0.
                  case_eq (typecheck G t1); intros.
                  * rewrite H2 in H0. easy.
                  * rewrite H2 in H0. easy.
           ++ case_eq (typecheck G t3); intros.
              +++ apply IHt3 with (T := t). easy. easy.
              +++ cbn in H0. rewrite H1 in H0.
                  case_eq (typecheck G t1); case_eq(typecheck G t2); intros; rewrite H2, H3 in H0; easy.
       - cbn in H. cbn in H0.
         case_eq (typecheck G t); intros.
         + specialize (IHt x t0 G H H1). easy.
         + rewrite H1 in H0. easy.
       - cbn in H. cbn in H0.
         apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq (typecheck G t2); intros.
           ++ destruct H.
              * specialize (IHt1 x t G H H1). easy.
              * specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0. destruct (typecheck G t1). destruct t0; easy.
              easy.
         + rewrite H1 in H0. easy.
       - cbn in H. cbn in H0.
         apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq (typecheck G t2); intros.
           ++ destruct H.
              * specialize (IHt1 x t G H H1). easy.
              * specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0. destruct (typecheck G t1). destruct t0; easy.
              easy.
         + rewrite H1 in H0. easy.
       - cbn in H. cbn in H0.
         apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq (typecheck G t2); intros.
           ++ destruct H.
              * specialize (IHt1 x t G H H1). easy.
              * specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0. destruct (typecheck G t1). destruct t0; easy.
              easy.
         + rewrite H1 in H0. easy.
       - cbn in H. cbn in H0.
         apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq (typecheck G t2); intros.
           ++ destruct H.
              * specialize (IHt1 x t G H H1). easy.
              * specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0. destruct (typecheck G t1). destruct t0; easy.
              easy.
         + rewrite H1 in H0. easy.
       - cbn in H. cbn in H0.
         apply listE in H.
         case_eq (typecheck G t1); intros.
         + case_eq (typecheck G t2); intros.
           ++ destruct H.
              * specialize (IHt1 x t G H H1). easy.
              * specialize (IHt2 x t0 G H H2). easy.
           ++ rewrite H2 in H0. destruct (typecheck G t1). destruct t0; easy.
              easy.
         + rewrite H1 in H0. easy.
Qed.


Lemma subst_preserves_typing: forall (x: string) (t v: term) (T U: type) (G: ctx),
  typecheck (extend G x U) t = Some T ->
  typecheck nil v = Some U ->
(*   Bool.eqb (find x (fv v)) false = true -> *)
  typecheck G (subst t x v) = Some T.
Proof. intros x t.
       revert x.
       induction t; intros.
(* intros x v T U G H Ha H0. *)
       - cbn in *. case_eq (x =? s); intros.
         + rewrite H1 in H.
           rewrite String.eqb_sym in H1.
           rewrite H1.
           specialize (context_invariance nil G v T); intros.
           rewrite H2. easy. rewrite <- H. easy.
           intros y Hy. cbn.
           specialize (free_in_context v y T nil); intros.
           apply In1 in Hy.
           rewrite H in H0.
           specialize (H3 Hy H0).
           destruct H3. cbn in H3. easy.
         + rewrite H1 in H. rewrite String.eqb_sym in H1. rewrite H1.
           cbn. easy.
       - case_eq (s =? x); intros.
         + rewrite String.eqb_eq in H1.
           rewrite H1 in *.
           rewrite subst0.
           specialize (context_invariance ((x, U) :: G) G (Lambda x t t0)); intros. 
           apply H2. easy.
           intros y Hy.
           apply fv_neq in Hy. cbn.
           rewrite Hy. easy.
         + cbn. rewrite H1. cbn.
           cbn in H. unfold extend in *.
           cbn in *.

           case_eq (typecheck ((s, t) :: (x, U) :: G) t0); intros.
           rewrite H2 in H.
           unfold extend in *.

           specialize (IHt x v t1 U ((s, t) :: G)).
           apply cinv0 in H2.
           specialize (IHt H2). rewrite IHt. easy.
           easy. rewrite String.eqb_sym. easy.
           rewrite H2 in H. easy.
      - cbn. cbn in H.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             rewrite (IHt1 x v t U G).
             rewrite (IHt2 x v t0 U G).
             easy. 
             easy.
             easy.
             easy.
             easy.
          ++ rewrite H2 in H.
             case_eq t; intros; subst; easy.
        + rewrite H1 in H. easy.
      - cbn in *. easy.
      - cbn in *. easy.
      - cbn in *. unfold extend in *.
        case_eq (typecheck ((x, U) :: G) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck ((x, U) :: G) t2); intros.
          ++ rewrite H2 in H.
             case_eq (typecheck ((x, U) :: G) t3); intros. 
             +++ rewrite H3 in H.
                 rewrite (IHt1 x v t U G).
                 rewrite (IHt2 x v t0 U G).
                 rewrite (IHt3 x v t4 U G).
                 easy.
                 easy.
                 easy.
                 easy.
                 easy.
                 easy.
                 easy.
             +++ rewrite H3 in H. easy.
          ++ rewrite H2 in H. easy.
        + rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t); intros.
        specialize (IHt x v t0 U G H1 H0).
        rewrite IHt.
        destruct t0; rewrite H1 in H; easy.
        rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             specialize (IHt1 x v t U G H1 H0).
             specialize (IHt2 x v t0 U G H2 H0).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H2 in H.
             destruct t; easy.
        + rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             specialize (IHt1 x v t U G H1 H0).
             specialize (IHt2 x v t0 U G H2 H0).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H2 in H.
             destruct t; easy.
        + rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             specialize (IHt1 x v t U G H1 H0).
             specialize (IHt2 x v t0 U G H2 H0).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H2 in H.
             destruct t; easy.
        + rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             specialize (IHt1 x v t U G H1 H0).
             specialize (IHt2 x v t0 U G H2 H0).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H2 in H.
             destruct t; easy.
        + rewrite H1 in H. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H1 in H.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H2 in H.
             specialize (IHt1 x v t U G H1 H0).
             specialize (IHt2 x v t0 U G H2 H0).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H2 in H.
             destruct t; easy.
         + rewrite H1 in H. easy.
Qed.

Lemma AppAppE: forall t1 t2 T, 
typecheck nil (App t1 t2) = Some T ->
exists U, typecheck nil t1 = Some (Arrow U T).
Proof. intros.
       cbn in *.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           destruct t; try easy.
           case_eq (type_eqb t3 t0); intros.
           ++ rewrite H2 in H. 
              inversion H.
              apply type_eqb_eq in H2.
              subst. now exists t0.
           ++ rewrite H2 in H. easy.
         + rewrite H1 in H. destruct t; easy. 
       - rewrite H0 in H. easy.
Qed.

Lemma AppAppT: forall t1 t2 T U, 
typecheck nil (App t1 t2) = Some T ->
typecheck nil t1 = Some (Arrow U T) ->
typecheck nil t2 = Some U.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       rewrite H0 in H.
       case_eq (typecheck nil t2); intros.
       rewrite H2 in H.
       case_eq t; intros.
       - case_eq (type_eqb U t0 ); intros.
         ++ apply type_eqb_eq in H4. subst. easy.
         ++ rewrite H4 in H. easy.
       - case_eq (type_eqb U t0 ); intros.
         ++ apply type_eqb_eq in H4. subst. easy.
         ++ rewrite H4 in H. easy.
       - case_eq (type_eqb U t0 ); intros.
         ++ apply type_eqb_eq in H4. subst. easy.
         ++ rewrite H4 in H. easy.
       - rewrite H2 in H. easy.
       - rewrite H1 in H. easy.
Qed.

Lemma fixTyping: forall t T, typecheck nil (Fix t) = Some T -> typecheck nil t = Some (Arrow T T).
Proof. intro t.
       induction t; intros; try (cbn in *; easy).
       - cbn in *.
         case_eq (typecheck (extend nil s t) t0); intros.
         + rewrite H0 in H.
           case_eq (type_eqb t t1); intros.
           ++ apply type_eqb_eq in H1.
              subst. rewrite type_eqb_refl in H.
              inversion H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in *.
         case_eq (typecheck nil t1); intros.
         + rewrite H0 in H.
           destruct t. easy. easy.
           case_eq (typecheck nil t2); intros.
           ++ rewrite H1 in H.
              case_eq (type_eqb t3 t); intros.
              * rewrite H2 in H.
                destruct t4. easy. easy.
                case_eq (type_eqb t4_1 t4_2); intros.
                rewrite H3 in H.
                inversion H. subst.
                apply type_eqb_eq in H3. subst. easy.
                rewrite H3 in H. easy.
              * rewrite H2 in H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in H.
         case_eq (typecheck nil t1); intros.
         + rewrite H0 in H.
           case_eq (typecheck nil t2); intros.
           ++ rewrite H1 in H.
              case_eq (typecheck nil t3); intros.
              * rewrite H2 in H.
                case_eq (type_eqb t Bool && type_eqb t0 t4 ); intros.
                rewrite H3 in H.
                destruct t0. easy. easy.
                case_eq (type_eqb t0_1 t0_2); intros.
                rewrite H4 in H.
                inversion H.
                cbn. rewrite H0, H1, H2, H3.
                apply type_eqb_eq in H4. subst. easy.
                rewrite H4 in H. easy.
                rewrite H3 in H. easy.
              * rewrite H2 in H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t); intros.
         + rewrite H0 in H. 
           destruct t0. easy. easy.
           case_eq (type_eqb t0_1 t0_2); intros.
           rewrite H1 in H.
           destruct t0_2. easy. easy.
           case_eq (type_eqb t0_2_1 t0_2_2); intros.
           rewrite H2 in H. inversion H.
           apply type_eqb_eq in H2. subst. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t1 ); intros.
         + rewrite H0 in H.
           destruct t.
           case_eq (typecheck nil t2); intros.
           rewrite H1 in H.
           destruct t. easy. easy. easy.
           rewrite H1 in H. easy. easy. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t1 ); intros.
         + rewrite H0 in H.
           destruct t.
           case_eq (typecheck nil t2); intros.
           rewrite H1 in H.
           destruct t. easy. easy. easy.
           rewrite H1 in H. easy. easy. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t1 ); intros.
         + rewrite H0 in H.
           destruct t.
           case_eq (typecheck nil t2); intros.
           rewrite H1 in H.
           destruct t. easy. easy. easy.
           rewrite H1 in H. easy. easy. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t1 ); intros.
         + rewrite H0 in H.
           destruct t.
           case_eq (typecheck nil t2); intros.
           rewrite H1 in H.
           destruct t. easy. easy. easy.
           rewrite H1 in H. easy. easy. easy.
         + rewrite H0 in H. easy.
       - cbn in H. cbn.
         case_eq (typecheck nil t1 ); intros.
         + rewrite H0 in H.
           destruct t.
           case_eq (typecheck nil t2); intros.
           rewrite H1 in H.
           destruct t. easy. easy. easy.
           rewrite H1 in H. easy. easy. easy.
         + rewrite H0 in H. easy.
Qed.


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
              specialize (AppAppE t1 t2 T H); intros.
              destruct H2 as (U, H2).
              specialize (AppAppT t1 t2 T U H H2); intros.
              specialize (subst_preserves_typing x e t2 T U nil); intros.
              rewrite H5.
              +++ easy.
              +++ rewrite Ht1 in H2. cbn in H2.
                  case_eq (typecheck (extend nil x tx) e); intros.
                  * rewrite H6 in H2.
                    inversion H2. subst. easy.
                  * rewrite H6 in H2. contradict H2; easy.
              +++ easy.
           ++ rewrite H1 in H0.
              specialize (AppAppE t1 t2 T H); intros.
              destruct H2 as (U, H2).
              specialize (AppAppT t1 t2 T U H H2); intros.
              specialize (progress t2 U H3); intros.
              destruct H4 as [H4 | H4].
              +++ rewrite H4 in H1. contradict H1; easy.
              +++ destruct H4 as (t2', H4).
                  rewrite H4 in H0.
                  inversion H0. cbn.
                  rewrite Ht1 in H2.
                  cbn in H2. rewrite H2.
                  specialize (IHt2 t2' U H3 H4).
                  rewrite IHt2, type_eqb_refl. easy.
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
              rewrite <- Ht1 in H1. cbn.
              specialize (AppAppT t1 t2 T U H H2); intros.
              specialize (IHt1 t1' (Arrow U T) H2 H3).
              rewrite IHt1, H4, type_eqb_refl. easy.
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
              rewrite <- Ht1 in H1. cbn.
              specialize (AppAppT t1 t2 T U H H2); intros.
              specialize (IHt1 e1' (Arrow U T) H2 H3).
              rewrite IHt1, H4, type_eqb_refl. easy.
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
              rewrite <- Ht1 in H1. cbn.
              specialize (AppAppT t1 t2 T U H H2); intros.
              specialize (IHt1 t1' (Arrow U T) H2 H3).
              rewrite IHt1, H4, type_eqb_refl. easy.
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
