
From SFL Require Import Imports Auxiliaries Terms.
Require Import Coq.Strings.String.

Definition ctx := list (string * type)%type.

Definition extend (c: ctx) (x: string) (t: type) :=
  (x, t) :: c.

Fixpoint lookup {A: Type} (c: list (string * A)) (s: string): option A :=
  match c with
    | nil => None
    | (x, t) :: r => if eqb x s then Some t else (lookup r s)
  end.


Fixpoint typecheck (m: ctx) (e: term): option type :=
match e with
  | Ident s       => lookup m s
  | Lambda x t e1 => let n := extend m x t in
                     let te1 := typecheck n e1 in
                     match te1 with
                       | Some te1 => Some (Arrow t te1)
                       | None => None 
                     end
  | App e1 e2     => let te1 := typecheck m e1 in
                     let te2 := typecheck m e2 in
                     match te1, te2 with
                       | Some (Arrow te1s te1t), Some te2 =>
                           if type_eqb te1s te2 then Some te1t else None
                       | _, _  => None
                     end
  | NVal n         => Some Int
  | BVal b         => Some Bool
  | ITE e1 e2 e3   => let te1 := typecheck m e1 in
                      let te2 := typecheck m e2 in
                      let te3 := typecheck m e3 in
                      match te1, te2, te3 with
                        | Some nte1, Some nte2, Some nte3 => 
                          if type_eqb nte1 Bool && type_eqb nte2 nte3 then Some nte2 else None
                        | _, _, _    => None 
                      end
   | Fix f         =>  let tf := typecheck m f in
                       match tf with
                         | Some (Arrow t1 t2) => if type_eqb t1 t2 then Some t2 else None
                         | _                  => None
                       end
   | Plus a b      => let t1 := typecheck m a in
                      let t2 := typecheck m b in
                      match t1, t2 with
                        | Some Int, Some Int => Some Int
                        | _, _               => None
                      end
   | Minus a b     => let t1 := typecheck m a in
                      let t2 := typecheck m b in
                      match t1, t2 with
                        | Some Int, Some Int => Some Int
                        | _, _               => None
                      end
   | Mult a b      => let t1 := typecheck m a in
                      let t2 := typecheck m b in
                      match t1, t2 with
                        | Some Int, Some Int => Some Int
                        | _, _               => None
                      end
   | Eq a b        => let t1 := typecheck m a in
                      let t2 := typecheck m b in
                      match t1, t2 with
                        | Some Int, Some Int => Some Bool
                        | _, _               => None
                      end
   | Gt a b        => let t1 := typecheck m a in
                      let t2 := typecheck m b in
                      match t1, t2 with
                        | Some Int, Some Int => Some Bool
                        | _, _               => None
                      end
end.


Lemma istypechecked_app: forall t1 t2 T, 
typecheck nil (App t1 t2) = Some T ->
exists U, typecheck nil t1 = Some (Arrow U T) /\
typecheck nil t2 = Some U.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
           case_eq (type_eqb t3 t0); intros.
           ++ rewrite H2 in H. 
              inversion H.
              apply type_eqb_eq in H2.
              subst. now exists t0.
           ++ rewrite H2 in H. contradict H; easy.
         + rewrite H1 in H. destruct t; contradict H; easy. 
       - rewrite H0 in H. contradict H; easy.
Qed.


Lemma istypechecked_ite: forall (t1 t2 t3: term) T, typecheck nil (ITE t1 t2 t3) = Some T ->
  typecheck nil t1 = Some Bool /\ typecheck nil t2 = Some T /\ typecheck nil t3 = Some T.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           case_eq (typecheck nil t3); intros.
           ++ rewrite H2 in H.
              case_eq (type_eqb t Bool && type_eqb t0 t4); intros.
              +++ rewrite H3 in H.
                  inversion H.
                  apply Bool.andb_true_iff in H3.
                  destruct H3 as (Ha, Hb).
                  apply type_eqb_eq in Ha.
                  apply type_eqb_eq in Hb.
                  subst. easy.
              +++ rewrite H3 in H. contradict H; easy.
           ++ rewrite H2 in H. contradict H; easy.
         + rewrite H1 in H. contradict H; easy.
       - rewrite H0 in H. contradict H; easy.
Qed.


Lemma istypechecked_fix: forall t T, typecheck nil (Fix t) = Some T -> typecheck nil t = Some (Arrow T T).
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t); intros.
       + rewrite H0 in H.
         destruct t0; try contradiction H; try easy.
         case_eq (type_eqb t0_1 t0_2); intros.
         ++ rewrite H1 in H.
            inversion H. apply type_eqb_eq in H1. subst.
            easy.
         ++ rewrite H1 in H. contradict H; easy.
       + rewrite H0 in H. contradict H; easy.
Qed.

Lemma istypechecked_plus: forall (t1 t2: term) T, typecheck nil (Plus t1 t2) = Some T ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int /\ T = Int.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
           destruct t0; try (contradict H; easy).
           inversion H. easy.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
       - rewrite H0 in H.
         contradict H; easy.
Qed.

Lemma istypechecked_minus: forall (t1 t2: term) T, typecheck nil (Minus t1 t2) = Some T ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int /\ T = Int.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
           destruct t0; try (contradict H; easy).
           inversion H. easy.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
       - rewrite H0 in H.
         contradict H; easy.
Qed.


Lemma istypechecked_mult: forall (t1 t2: term) T, typecheck nil (Mult t1 t2) = Some T ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int /\ T = Int.
Proof. intros.
       cbn in H.
       case_eq (typecheck nil t1); intros.
       - rewrite H0 in H.
         case_eq (typecheck nil t2); intros.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
           destruct t0; try (contradict H; easy).
           inversion H. easy.
         + rewrite H1 in H.
           destruct t; try (contradict H; easy).
       - rewrite H0 in H.
         contradict H; easy.
Qed.


Lemma istypechecked_eq: forall (t1 t2: term) T, typecheck nil (Eq t1 t2) = Some T ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int /\ T = Bool.
Proof. intro t1.
       cbn.
       case_eq (typecheck nil t1); intros; try easy.
       case_eq t; intros.
       + rewrite H1 in H0.
         case_eq (typecheck nil t2); intros.
         ++ rewrite H2 in H0.
            destruct t0. inversion H0. easy.
            easy.
            easy.
         ++ rewrite H2 in H0. easy.
       + rewrite H1 in H0. easy.
       + rewrite H1 in H0. easy.
Qed.


Lemma istypechecked_gt: forall (t1 t2: term) T, typecheck nil (Gt t1 t2) = Some T ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int /\ T = Bool.
Proof. intro t1.
       cbn.
       case_eq (typecheck nil t1); intros; try easy.
       case_eq t; intros.
       + rewrite H1 in H0.
         case_eq (typecheck nil t2); intros.
         ++ rewrite H2 in H0.
            destruct t0. inversion H0. easy.
            easy.
            easy.
         ++ rewrite H2 in H0. easy.
       + rewrite H1 in H0. easy.
       + rewrite H1 in H0. easy.
Qed.

Lemma context_invariance: forall G K t T,
  typecheck G t = Some T ->
  (forall x, find x (fv t) = true -> lookup G x = lookup K x) ->
  typecheck K t = Some T.
Proof. intros G K t.
       revert G K.
       induction t; intros.
       - simpl in *. rewrite <- H.
         specialize (H0 s).
         symmetry. apply H0.
         now rewrite String.eqb_refl.
       - cbn. cbn in H. unfold extend in *.
         case_eq (typecheck ((s, t) :: G) t0); intros.
         specialize (IHt ((s, t) :: G) ((s, t) :: K) t1).
         rewrite IHt.
         rewrite H1 in H. easy.
         easy.
         intros x Hx. cbn.
         case_eq ( s =? x ); intros.
         + easy.
         + apply H0. apply find_lam_fv; easy.
         + rewrite H1 in H. easy.
       - cbn. cbn in H.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H. 
              specialize (IHt1 G K t).
              rewrite IHt1.
              specialize (IHt2 G K t0).
              rewrite IHt2. easy.
              easy.
              intros. apply H0.
              cbn. apply In1.
              apply In1 in H3.
              cbn. 
              specialize (In5 (fv t1 ++ fv t2)); intros.
              apply H4. apply In7. easy.
              easy.
              intros. apply H0.
              cbn.
              apply In1.
              apply In1 in H3.
              specialize (In5 (fv t1 ++ fv t2)); intros.
              apply H4. apply In6. easy.
           ++ rewrite H2 in H.
              case_eq t; intros; subst; easy.
         + rewrite H1 in H. easy.
       - cbn in *. easy.
       - cbn in *. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              case_eq (typecheck G t3); intros.
              +++ rewrite H3 in H.
                  rewrite (IHt1 G K t).
                  rewrite (IHt2 G K t0).
                  rewrite (IHt3 G K t4).
                  easy.
                  easy.
                  intros. apply H0.
                  apply In1.
                  apply In1 in H4.
                  specialize (In5 (fv t1 ++ fv t2 ++ fv t3)); intros.
                  apply H5.
                  do 2 apply In7. easy.
                  easy.
                  intros. apply H0.
                  apply In1.
                  apply In1 in H4.
                  specialize (In5 (fv t1 ++ fv t2 ++ fv t3)); intros.
                  apply H5.
                  apply In7.
                  apply In6. easy.
                  easy.
                  intros. apply H0.
                  apply In1.
                  apply In1 in H4.
                  specialize (In5 (fv t1 ++ fv t2 ++ fv t3)); intros.
                  apply H5.
                  apply In6. easy.
              +++ rewrite H3 in H. easy. 
           ++ rewrite H2 in H. easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t ); intros.
         + specialize (IHt G K t0 H1).
           rewrite IHt.
           case_eq t0; intros; subst; rewrite H1 in H; easy.
           intros y Hy.
           apply H0. easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              specialize (IHt1 G K t H1).
              specialize (IHt2 G K t0 H2).
              rewrite IHt1, IHt2. easy.
              intros y Hy. apply H0.
              apply In1, In5, In7.
              apply In1 in Hy. easy.
              intros y Hy. apply H0.
              apply In1, In5, In6.
              apply In1 in Hy. easy.
           ++ rewrite H2 in H.
              destruct t; easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              specialize (IHt1 G K t H1).
              specialize (IHt2 G K t0 H2).
              rewrite IHt1, IHt2. easy.
              intros y Hy. apply H0.
              apply In1, In5, In7.
              apply In1 in Hy. easy.
              intros y Hy. apply H0.
              apply In1, In5, In6.
              apply In1 in Hy. easy.
           ++ rewrite H2 in H.
              destruct t; easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              specialize (IHt1 G K t H1).
              specialize (IHt2 G K t0 H2).
              rewrite IHt1, IHt2. easy.
              intros y Hy. apply H0.
              apply In1, In5, In7.
              apply In1 in Hy. easy.
              intros y Hy. apply H0.
              apply In1, In5, In6.
              apply In1 in Hy. easy.
           ++ rewrite H2 in H.
              destruct t; easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              specialize (IHt1 G K t H1).
              specialize (IHt2 G K t0 H2).
              rewrite IHt1, IHt2. easy.
              intros y Hy. apply H0.
              apply In1, In5, In7.
              apply In1 in Hy. easy.
              intros y Hy. apply H0.
              apply In1, In5, In6.
              apply In1 in Hy. easy.
           ++ rewrite H2 in H.
              destruct t; easy.
         + rewrite H1 in H. easy.
       - cbn in *.
         case_eq (typecheck G t1); intros.
         + rewrite H1 in H.
           case_eq (typecheck G t2); intros.
           ++ rewrite H2 in H.
              specialize (IHt1 G K t H1).
              specialize (IHt2 G K t0 H2).
              rewrite IHt1, IHt2. easy.
              intros y Hy. apply H0.
              apply In1, In5, In7.
              apply In1 in Hy. easy.
              intros y Hy. apply H0.
              apply In1, In5, In6.
              apply In1 in Hy. easy.
           ++ rewrite H2 in H.
              destruct t; easy.
         + rewrite H1 in H. easy.
Qed.

Lemma fv_neq: forall t x y T,
  find y (fv (Lambda x T t)) = true -> String.eqb x y = false.
Proof. intros.
       apply In1 in H. cbn in H.
       apply List.filter_In in H.
       destruct H.
       case_eq ((y =? x)); intros.
       + rewrite H1 in H0. cbn in H0. easy.
       + now rewrite String.eqb_sym in H1.
Qed.


Lemma context_assoc: forall t x s T T2 U G,
  String.eqb x s = false ->
  typecheck ((s, T) :: (x, U) :: G) t = Some T2 ->
  typecheck ((x, U) :: (s, T) :: G) t = Some T2.
Proof. intros.
       specialize (context_invariance ((s, T) :: (x, U) :: G)  ((x, U) :: (s, T) :: G) t T2); intros.
       apply H1.
       easy.
       intros y Hy. cbn.
       case_eq (s =? y); intros.
       + rewrite String.eqb_eq in H2.
         rewrite H2 in H. rewrite H. easy.
       + easy.
Qed.


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


Lemma subst_preserves_typing: forall (t v: term) (x: string)  (T U: type) (G: ctx),
  typecheck (extend G x U) t = Some T ->
  typecheck nil v = Some U ->
  typecheck G (subst t x v) = Some T.
Proof. intro t.
       induction t; intros v x T U G Ha Hb.
       - cbn.
         case_eq (x =? s); intros.
         + apply String.eqb_eq in H.
           rewrite H in *.
           cbn in Ha.
           rewrite String.eqb_refl in Ha.
           rewrite String.eqb_refl.
           rewrite <- Ha.
           specialize (context_invariance nil G v U); intros.
           rewrite H0. easy. exact Hb.
           intros y Hy. cbn.
           specialize (free_in_context v y T nil); intros.
           apply In1 in Hy.
           rewrite Ha in Hb.
           specialize (H1 Hy Hb).
           destruct H1. cbn in H1. easy.
         + cbn in Ha. rewrite H in Ha.
           rewrite String.eqb_sym in H. rewrite H.
           cbn. easy.
       - case_eq (s =? x); intros.
         + rewrite String.eqb_eq in H.
           rewrite H in *.
           assert (seq: subst (Lambda x t t0) x v = (Lambda x t t0) ).
           { cbn. rewrite String.eqb_refl. cbn. easy. } 
           rewrite seq.
           specialize (context_invariance ((x, U) :: G) G (Lambda x t t0) T Ha); intros. 
           apply H0.
           intros y Hy.
           apply fv_neq in Hy. cbn.
           rewrite Hy. easy.
         + cbn. rewrite H. cbn.
           cbn in Ha. unfold extend in *.
           case_eq (typecheck ((s, t) :: (x, U) :: G) t0); intros.
           rewrite H0 in Ha.
           unfold extend in *.
           apply context_assoc in H0.
           specialize (IHt v x t1 U ((s, t) :: G) H0 Hb).
           rewrite IHt; easy.
           rewrite String.eqb_sym. easy.
           rewrite H0 in Ha. easy.
      - cbn. cbn in Ha.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. exact Ha.
          ++ rewrite H0 in Ha.
             case_eq t; intros; subst; easy.
        + rewrite H in Ha. easy.
      - cbn in *. easy.
      - cbn in *. easy.
      - cbn in *. unfold extend in *.
        case_eq (typecheck ((x, U) :: G) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck ((x, U) :: G) t2); intros.
          ++ rewrite H0 in Ha.
             case_eq (typecheck ((x, U) :: G) t3); intros. 
             +++ rewrite H1 in Ha.
                 specialize (IHt1 v x t U G H Hb).
                 specialize (IHt2 v x t0 U G H0 Hb).
                 specialize (IHt3 v x t4 U G H1 Hb).
                 rewrite IHt1, IHt2, IHt3.
                 exact Ha.
             +++ rewrite H1 in Ha. easy.
          ++ rewrite H0 in Ha. easy.
        + rewrite H in Ha. easy.
      - cbn.
        case_eq (typecheck (extend G x U) t); intros.
        + specialize (IHt v x t0 U G H Hb).
          rewrite IHt.
          cbn in Ha.
          rewrite H in Ha.
          exact Ha.
        + cbn in Ha.
          rewrite H in Ha. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H0 in Ha.
             destruct t; easy.
        + rewrite H in Ha. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H0 in Ha.
             destruct t; easy.
        + rewrite H in Ha. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H0 in Ha.
             destruct t; easy.
        + rewrite H in Ha. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H0 in Ha.
             destruct t; easy.
        + rewrite H in Ha. easy.
      - cbn in *.
        case_eq (typecheck (extend G x U) t1); intros.
        + rewrite H in Ha.
          case_eq (typecheck (extend G x U) t2); intros.
          ++ rewrite H0 in Ha.
             specialize (IHt1 v x t U G H Hb).
             specialize (IHt2 v x t0 U G H0 Hb).
             rewrite IHt1, IHt2. easy.
          ++ rewrite H0 in Ha.
             destruct t; easy.
        + rewrite H in Ha. easy.
Qed.


Definition factorial := 
                Lambda "f" (Arrow Int Int)
                 (Lambda "x" Int 
                   (ITE (Gt (Ident "x") (NVal 1)) 
                        (Mult (Ident "x") (App (Ident "f") (Minus (Ident "x") (NVal 1))))
                        (NVal 1))
                  ).

Compute (typecheck nil (Fix factorial)).

Compute (typecheck nil (App (NVal 5) (ITE (NVal 3) (NVal 5) (NVal 10)))).


   