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

Lemma AppT: forall t t2 T U s, 
typecheck nil (App (Lambda s T t) t2) = Some U ->
Some T = typecheck nil t2.
Proof. intros t t2 T.
       revert t t2.
       induction T; intros.
       - cbn in *.
         case_eq (typecheck (extend nil s Int) t); intros.
         + rewrite H0 in H.
           case_eq (typecheck nil t2 ); intros.
           ++ rewrite H1 in H.
              case_eq (type_eqb Int t1); intros.
              +++ apply type_eqb_eq in H2. rewrite H2. easy.
              +++ rewrite H2 in H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in *.
         case_eq (typecheck (extend nil s Bool) t ); intros.
         + rewrite H0 in H.
           case_eq (typecheck nil t2 ); intros.
           ++ rewrite H1 in H.
              case_eq (type_eqb Bool t1); intros.
              +++ apply type_eqb_eq in H2. rewrite H2. easy.
              +++ rewrite H2 in H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
       - cbn in H.
         case_eq (typecheck (extend nil s (Arrow T1 T2)) t); intros.
         + rewrite H0 in H.
           case_eq (typecheck nil t2); intros.
           ++ rewrite H1 in H.
              case_eq (type_eqb (Arrow T1 T2) t1); intros.
              +++ apply type_eqb_eq in H2. rewrite H2. easy.
              +++ rewrite H2 in H. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
Qed.


Lemma AppT2: forall t T U s, 
typecheck nil (Lambda s T t) = Some (Arrow T U) <->
Some U = typecheck ((s, T) :: nil) t.
Proof. split.
       - intros.
         cbn in *. unfold extend in *.
         case_eq (typecheck ((s, T) :: nil) t); intros.
         + rewrite H0 in H.
           inversion H. easy.
         + rewrite H0 in H. easy.
       - intros.
         cbn in *. unfold extend in *.
         rewrite <- H. easy.
Qed.

Lemma AppT3: forall t t2 T U s, 
typecheck nil (App (Lambda s T t) t2) = Some U ->
Some U = typecheck ((s, T) :: nil) t.
Proof.  intros.
        specialize (AppT _ _ _ _ _ H); intros.
        apply AppT2. cbn in *. unfold extend in *.
        case_eq (typecheck ((s, T) :: nil) t); intros.
        - rewrite H1, <- H0 in H.
          rewrite type_eqb_refl in H.
          now inversion H.
        - rewrite H1 in H. easy.
Qed.


Lemma AppT4: forall t t2 T U s, 
typecheck nil (App (Lambda s T t) t2) = Some U ->
Some U = typecheck nil (subst t s t2).
Proof. intros.
       specialize (AppT _ _ _ _ _ H); intros.
       specialize (AppT3 _ _ _ _ _ H); intros.
       specialize (subst_preserves_typing s t t2 U T nil); intros.
       rewrite H2. easy.
       unfold extend in *. easy.
       easy.
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

(* Lemma AppZ: forall t T U s, 
typecheck nil (App (Lambda s T t) Zero) = Some U ->
T = Int.
Proof. intros t T.
       induction T; intros.
       - easy.
       - cbn in H.
         case_eq (typecheck (extend nil s Bool) t); intros.
         rewrite H0 in H.
         cbn in H. easy.
         rewrite H0 in H. easy.
       - cbn in H.
         case_eq (typecheck (extend nil s (Arrow T1 T2)) t); intros.
         + rewrite H0 in H. cbn in H. easy.
         + rewrite H0 in H. easy.
Qed. *)

Lemma App_L2: forall x T e1 e2,
  isvalue e2 = false ->
  match beta e2 with
    | Some e2' => beta (App (Lambda x T e1) e2) = Some (App (Lambda x T e1) e2')
    | None     => beta (App (Lambda x T e1) e2)= None
  end.
Proof. intros.
       cbn. rewrite H.
       case_eq (beta e2 ); intros.
       + easy.
       + easy.
Qed.

Lemma AppApp_L2: forall e1 e2,
  isvalue e1 = false ->
  match beta e1 with
    | Some e1' => beta (App e1 e2) = Some (App e1' e2)
    | None     => beta (App e1 e2) = None
  end.
Proof. intros.
       cbn. rewrite H.
       case_eq (beta e1 ); intros.
       + case_eq e1; intros; try easy.
         subst. cbn in *. easy.
       + case_eq e1; intros; try easy.
         subst. cbn in *. easy.
Qed.

Lemma AppApp_TL2: forall e1 e2 e1',
  isvalue e1 = false ->
  beta e1 = Some e1' -> 
  beta (App e1 e2) = Some (App e1' e2).
Proof. intros.
       cbn. rewrite H0.
       + case_eq e1; intros; try (subst; cbn in *; easy).
Qed.

Definition isLambda (t: term): bool :=
  match t with
    | Lambda x T t0 => true
    | _             => false
  end.

(* Definition isFix (t: term): bool :=
  match t with
    | Fix f x T e T2 => true
    | _              => false
  end.
 *)

Lemma AppApp_TL1: forall e1 e2 e2',
  isvalue e1 = true ->
  isLambda e1 = false ->
  beta e2 = Some e2' -> 
  beta (App e1 e2) = Some (App e1 e2').
Proof. intros.
       cbn. rewrite H1.
       + case_eq e1; intros; try (subst; cbn in *; easy).
Qed.


Lemma AppApp_TL3: forall e1 e2 e2',
  isvalue e2 = false ->
  isLambda e1 = true ->
  beta e2 = Some e2' -> 
  beta (App e1 e2) = Some (App e1 e2').
Proof. intros.
       cbn. rewrite H1.
       + case_eq e1; intros; try (subst; cbn in *; easy).
         cbn. rewrite H. easy.
Qed.


Lemma ITEA: forall e1 e2 e3 T,
  typecheck nil (ITE e1 e2 e3) = Some T ->
  typecheck nil e1 = Some Bool /\ typecheck nil e2 = Some T /\ typecheck nil e3 = Some T.
Proof. intros.
       cbn in *.
       case_eq(typecheck nil e1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil e2); intros.
         + rewrite H1 in H.
           case_eq (typecheck nil e3); intros.
           ++ rewrite H2 in H.
              case_eq(type_eqb t Bool); case_eq(type_eqb t0 t1); intros.
              * rewrite H3, H4 in H.
                cbn in H. rewrite H.
                apply type_eqb_eq in H3.
                apply type_eqb_eq in H4.
                subst. easy.
              * rewrite H3, H4 in H. cbn in H. easy.
              * rewrite H3, H4 in H. cbn in H. easy.
              * rewrite H3, H4 in H. cbn in H. easy.
           ++ rewrite H2 in H. easy.
         + rewrite H1 in H. easy.
       - rewrite H0 in H. easy.
Qed.

Corollary typable_empty__closed: forall t T,
    typecheck nil t = Some T ->
    forall x, find x (fv t) = false.
Proof. intros.
       case_eq (find x (fv t)); intros.
       - apply In1 in H0.
         specialize (free_in_context t x T nil H0 H); intros.
         destruct H1. cbn in H1. easy.
       - easy.
Qed.

(* Lemma subst_preserves_typing_nil: forall (x: string) (t v: term) (T U: type) (G: ctx),
  typecheck (extend G x U) t = Some T ->
  typecheck nil v = Some U ->
(*   Bool.eqb (find x (fv v)) false = true -> *)
  typecheck G (subst t x v) = Some T.
Proof. intros.
       specialize (subst_preserves_typing x t v T U G H); intros.
       apply H1.
       specialize (context_invariance nil G v U H0); intros.
       apply H2.
       intros y Hy. cbn.
       eapply typable_empty__closed with (x := y) in H0. rewrite H0 in Hy. easy.
Qed. *)

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

