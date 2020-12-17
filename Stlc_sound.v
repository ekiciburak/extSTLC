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
       - case_eq t1; case_eq t2; intros; rewrite H1, H2 in H; try (cbn in H, H0; easy).
         cbn in H, H0.
         rewrite H1, H2 in H0. cbn in H0.
         unfold extend in *.
         case_eq (match typecheck ((s0, t) :: nil) t0 with
          | Some te1 => Some (Arrow t te1)
          | None => None
          end ); intros.
          rewrite H3 in H. destruct t3; easy.
         rewrite H3 in H. easy.
         rewrite H1, H2 in H0. cbn in H0.
         inversion H0.
         unfold extend in *.
         specialize (subst_preserves_typing s0 t4 (Lambda s t t0) T t3 nil); intros.
         apply H3.
         unfold extend in *.
         cbn in H, H0.
         case_eq (typecheck ((s0, t3) :: nil) t4 ); intros.
         unfold extend in *.
         rewrite H5 in H.
         case_eq (typecheck ((s, t) :: nil) t0); intros.
         rewrite H6 in H.
         case_eq (type_eqb t3 (Arrow t t6)); intros.
         rewrite H7 in H. easy.
         rewrite H7 in H. easy.
         rewrite H6 in H. easy.
         unfold extend in *.
         rewrite H5 in H. easy.
         cbn. unfold extend in *.
         case_eq (typecheck ((s0, t3) :: nil) t4 ); intros.
         cbn in H, H0.
         unfold extend in *.
         rewrite H5 in H.
         case_eq (typecheck ((s, t) :: nil) t0); intros.
         rewrite H6 in H.
         case_eq (type_eqb t3 (Arrow t t6)); intros.
         apply type_eqb_eq in H7. rewrite H7. easy.
         rewrite H7 in H. easy.
         rewrite H6 in H. easy.
         unfold extend in *.
         cbn in H, H0.
         unfold extend in *.
         rewrite H5 in H. easy.

         specialize (AppT _ _ _ _ _ H); intros.
         specialize (AppT3 _ _ _ _ _ H); intros.
         specialize (AppT4 _ _ _ _ _ H); intros.
         symmetry in H3, H4, H5.
         cbn in H0. rewrite H2 in H0.
         assert (isvalue (App t t0) = false).
         { simpl. easy. }
         rewrite H1, H6 in H0.
         rewrite <- H1 in *.
         case_eq (beta t2); intros.
         rewrite H7 in H0.
         inversion H0.
         cbn. unfold extend.
         rewrite H4.
         assert (typecheck nil (App (Lambda s t3 t4) t5) = typecheck nil t').
         { rewrite H9. easy. }
         specialize (IHt2 t5 t3 H3 H7).
         rewrite IHt2. rewrite type_eqb_refl. easy.
         rewrite H7 in H0. easy.

         specialize (AppT _ _ _ _ _ H); intros.
         rewrite H1, H2 in *. cbn in H, H0.
         inversion H0.
         specialize (subst_preserves_typing s t0 (NVal n) T Int nil); intros.
         rewrite H4. easy.
         unfold extend in *.
         cbn in H3.
         inversion H3.
         rewrite H7 in H.
         case_eq (typecheck ((s, Int) :: nil) t0); intros.
         rewrite H6 in H. cbn in H. easy.
         rewrite H6 in H. easy.
         easy.

(**)
         specialize (AppT _ _ _ _ _ H); intros.
         rewrite H1, H2 in *. cbn in H, H0.
         inversion H0.
         specialize (subst_preserves_typing s t0 (BVal b) T Bool nil); intros.
         rewrite H4. easy.
         unfold extend in *.
         cbn in H3.
         inversion H3.
         rewrite H7 in H.
         case_eq (typecheck ((s, Bool) :: nil) t0); intros.
         rewrite H6 in H. cbn in H. easy.
         rewrite H6 in H. easy.
         easy.

(**)
         rewrite H1, H2 in H0.
         specialize (AppAppE  (Lambda s t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT  (Lambda s t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue  ((ITE t t0 t3)) = false).
         { easy. }

         specialize (App_L2 s t4 t5 (ITE t t0 t3) H5); intros.
         case_eq (beta (ITE t t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t6 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue  (Fix t) = false).
         { easy. }

         specialize (App_L2 s t0 t3 (Fix t) H5); intros.
         case_eq (beta (Fix t)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t4 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue  (Plus t t0) = false).
         { easy. }

         specialize (App_L2 s t3 t4 (Plus t t0) H5); intros.
         case_eq (beta (Plus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t5 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue  (Plus t t0) = false).
         { easy. }

         specialize (App_L2 s t3 t4 (Minus t t0) H5); intros.
         case_eq (beta (Minus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t5 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue  (Plus t t0) = false).
         { easy. }

         specialize (App_L2 s t3 t4 (Mult t t0) H5); intros.
         case_eq (beta (Mult t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t5 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue  (Eq t t0) = false).
         { easy. }

         specialize (App_L2 s t3 t4 (Eq t t0) H5); intros.
         case_eq (beta (Eq t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t5 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Lambda s t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Lambda s t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue  (Plus t t0) = false).
         { easy. }

         specialize (App_L2 s t3 t4 (Gt t t0) H5); intros.
         case_eq (beta (Gt t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H1 in IHt2.
         specialize (IHt2 t5 U H4 H7).
         cbn.
         cbn in H3.
         rewrite H3.
         rewrite IHt2.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


(**)
         rewrite H1, H2 in *.
         cbn in *.
         case_eq (      match typecheck nil t with
           | Some (Arrow te1s te1t) =>
             match typecheck nil t0 with
              | Some te2 => if type_eqb te1s te2 then Some te1t else None
              | None => None
             end
           | _ => None
          end); intros.
         rewrite H3 in H.
         destruct t3; easy.
         rewrite H3 in H. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Lambda s t t0)  T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4.
         rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (App t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t t0) (NVal n) T U H H3); intros.
         assert (isvalue (App t t0) = false).
         { easy. }
         specialize (AppApp_L2 (App t t0) (NVal n) H5); intros.
         case_eq (beta (App t t0)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t t0) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t t0) (BVal b) T U H H3); intros.
         assert (isvalue (App t t0) = false).
         { easy. }
         specialize (AppApp_L2 (App t t0) (BVal b) H5); intros.
         case_eq (beta (App t t0)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t t0) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.


         rewrite H1, H2 in H0.
         specialize (AppAppE (App t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (App t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (App t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (App t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t4 t5) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (App t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (App t0 t3) (Fix t) H5); intros.
         case_eq (beta (App t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t0 t3) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (App t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (App t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (App t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (App t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (App t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         rewrite H0 in H6.
         inversion H6.
         cbn. rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         specialize (progressR (App t3 t4) (Arrow U T) H3); intros.
         destruct H8. easy.
         destruct H8. rewrite H7 in H8. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t t0 t3) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t t0 t3) (Ident s) T U H H3); intros. easy.
(*          cbn in H3. easy.
         case_eq (typecheck nil t); intros.
         rewrite H5 in H3.
         case_eq (typecheck nil t0); intros.
         rewrite H6 in H3.
         case_eq (typecheck nil t3); intros.
         rewrite H7 in H3.
         case_eq (type_eqb t4 Bool && type_eqb t5 t6); intros.
         easy.
         rewrite H8 in H3. easy.
         rewrite H7 in H3. easy.
         rewrite H6 in H3. easy.
         rewrite H5 in H3. easy. *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Lambda s t t0) T U H H3); intros.

         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Lambda s t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4.
         case_eq (typecheck (extend nil s t) t0); intros.
         rewrite H8 in H4.
         inversion H4. 
         rewrite type_eqb_refl. easy.
         rewrite H8 in H4. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (App t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (App t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t t0 t3) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t t0 t3) (NVal n) T U H H3); intros.
         assert (isvalue  (ITE t t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t t0 t3) (NVal n) H5); intros.
         case_eq (beta (ITE t t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t t0 t3) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t t0 t3) (BVal b) T U H H3); intros.
         assert (isvalue  (ITE t t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t t0 t3) (BVal b) H5); intros.
         case_eq (beta (ITE t t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t4 t5 t6) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t4 t5 t6) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (ITE t4 t5 t6) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t4 t5 t6) (ITE t t0 t3) H5); intros.
         case_eq (beta (ITE t4 t5 t6)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t7 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t0 t3 t4) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t0 t3 t4) (Fix t) T U H H3); intros.
         assert (isvalue (ITE t0 t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t0 t3 t4) (Fix t) H5); intros.
         case_eq (beta (ITE t0 t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Plus t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Plus t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Minus t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Minus t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Mult t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Mult t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.


         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Eq t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Eq t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

         rewrite H1, H2 in H0.
         specialize (AppAppE (ITE t3 t4 t5) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (ITE t3 t4 t5) (Gt t t0) T U H H3); intros.
         assert (isvalue (ITE t3 t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (ITE t3 t4 t5) (Gt t t0) H5); intros.
         case_eq (beta (ITE t3 t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7, H0 in H6. easy.

(** App (Fix, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t) (Ident s) T U H H3); intros.
         assert (isvalue (Fix t) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t) (Ident s) H5); intros.
         case_eq (beta (Fix t)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t0 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy.
         rewrite H7 in H6. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Lambda s t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (App t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (App t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t) (NVal n) T U H H3); intros.
         assert (isvalue (Fix t) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t) (NVal n) H5); intros.
         case_eq (beta (Fix t)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t0 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t) (BVal b) T U H H3); intros.
         assert (isvalue (Fix t) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t) (BVal b) H5); intros.
         case_eq (beta (Fix t)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t0 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t4) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t4) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Fix t4) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t4) (ITE t t0 t3) H5); intros.
         case_eq (beta (Fix t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t0) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t0) (Fix t) T U H H3); intros.
         assert (isvalue (Fix t0) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t0) (Fix t) H5); intros.
         case_eq (beta (Fix t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)
         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Plus t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Plus t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Minus t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Minus t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Mult t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Mult t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Eq t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Eq t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Fix t3) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Fix t3) (Gt t t0) T U H H3); intros.
         assert (isvalue (Fix t3) = false).
         { easy. }
         specialize (AppApp_L2 (Fix t3) (Gt t t0) H5); intros.
         case_eq (beta (Fix t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy.
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

(** App (Plus, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t t0) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t t0) (Ident s) T U H H3); intros.
         assert (isvalue (Plus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t t0) (Ident s) H5); intros.
         case_eq (beta (Plus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (App t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t t0) (NVal n) T U H H3); intros.
         assert (isvalue (Plus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t t0) (NVal n) H5); intros.
         case_eq (beta (Plus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t t0) (BVal b) T U H H3); intros.
         assert (isvalue (Plus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t t0) (BVal b) H5); intros.
         case_eq (beta (Plus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Plus t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (Plus t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (Plus t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t0 t3) (Fix t) H5); intros.
         case_eq (beta (Plus t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Plus t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Plus t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Plus t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (Plus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.


(** App (Minus, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t t0) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t t0) (Ident s) T U H H3); intros.
         assert (isvalue (Minus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t t0) (Ident s) H5); intros.
         case_eq (beta (Minus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (App t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t t0) (NVal n) T U H H3); intros.
         assert (isvalue (Minus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t t0) (NVal n) H5); intros.
         case_eq (beta (Minus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t t0) (BVal b) T U H H3); intros.
         assert (isvalue (Minus t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t t0) (BVal b) H5); intros.
         case_eq (beta (Minus t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Minus t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (Minus t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (Minus t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t0 t3) (Fix t) H5); intros.
         case_eq (beta (Minus t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Minus t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Minus t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Minus t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (Minus t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.


(**)
(** App (Mult, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t t0) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t t0) (Ident s) T U H H3); intros.
         assert (isvalue (Mult t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t t0) (Ident s) H5); intros.
         case_eq (beta (Mult t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (App t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t t0) (NVal n) T U H H3); intros.
         assert (isvalue (Mult t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t t0) (NVal n) H5); intros.
         case_eq (beta (Mult t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t t0) (BVal b) T U H H3); intros.
         assert (isvalue (Mult t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t t0) (BVal b) H5); intros.
         case_eq (beta (Mult t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Mult t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (Mult t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (Mult t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t0 t3) (Fix t) H5); intros.
         case_eq (beta (Mult t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (Plus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Mult t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Mult t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (Minus t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Mult t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (Mult t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.


(** App (Eq, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t t0) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t t0) (Ident s) T U H H3); intros.
         assert (isvalue (Eq t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t t0) (Ident s) H5); intros.
         case_eq (beta (Eq t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (Mult t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (App t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t t0) (NVal n) T U H H3); intros.
         assert (isvalue (Eq t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t t0) (NVal n) H5); intros.
         case_eq (beta (Eq t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t t0) (BVal b) T U H H3); intros.
         assert (isvalue (Eq t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t t0) (BVal b) H5); intros.
         case_eq (beta (Eq t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Eq t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (Eq t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (Eq t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t0 t3) (Fix t) H5); intros.
         case_eq (beta (Eq t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Eq t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Eq t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Eq t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (Eq t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(** App (Gt, t) *)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t t0) (Ident s) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t t0) (Ident s) T U H H3); intros.
         assert (isvalue (Gt t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t t0) (Ident s) H5); intros.
         case_eq (beta (Gt t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Lambda s t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Lambda s t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Lambda s t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (App t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (App t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (App t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t t0) (NVal n) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t t0) (NVal n) T U H H3); intros.
         assert (isvalue (Gt t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t t0) (NVal n) H5); intros.
         case_eq (beta (Gt t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t t0) (BVal b) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t t0) (BVal b) T U H H3); intros.
         assert (isvalue (Gt t t0) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t t0) (BVal b) H5); intros.
         case_eq (beta (Gt t t0)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t3 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. inversion H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t4 t5) (ITE t t0 t3) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t4 t5) (ITE t t0 t3) T U H H3); intros.
         assert (isvalue (Gt t4 t5) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t4 t5) (ITE t t0 t3) H5); intros.
         case_eq (beta (Gt t4 t5)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t6 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t0 t3) (Fix t) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t0 t3) (Fix t) T U H H3); intros.
         assert (isvalue (Gt t0 t3) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t0 t3) (Fix t) H5); intros.
         case_eq (beta (Gt t0 t3)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t4 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Plus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Plus t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Plus t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Minus t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Minus t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Minus t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Mult t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Mult t t0) T U H H3); intros.
         assert (isvalue (Eq t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Mult t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Eq t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Eq t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Eq t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

(**)

         rewrite H1, H2 in H0.
         specialize (AppAppE (Gt t3 t4) (Gt t t0) T H); intros.
         destruct H3 as (U, H3).
         specialize (AppAppT (Gt t3 t4) (Gt t t0) T U H H3); intros.
         assert (isvalue (Gt t3 t4) = false).
         { easy. }
         specialize (AppApp_L2 (Gt t3 t4) (Gt t t0) H5); intros.
         case_eq (beta (Gt t3 t4)); intros.
         rewrite H7 in H6.
         rewrite H0 in H6.
         inversion H6.
         rewrite H2 in IHt1.
         specialize (IHt1 t5 (Arrow U T) H3 H7).
         cbn.
         rewrite IHt1.
         cbn in H4. rewrite H4.
         rewrite type_eqb_refl. easy. 
         rewrite H7 in H6.
         rewrite H6 in H0. easy.

      - cbn in H0. inversion H0.
      - cbn in H0. inversion H0.


      - specialize (ITEA t1 t2 t3 T H); intros.
        destruct H1 as (Ha, (Hb, Hc)).
        cbn in H0.
        case_eq t1; intros; rewrite H1 in Ha.
        * easy.
        * cbn in Ha.
          case_eq (typecheck (extend nil s t) t0 ); intros.
          rewrite H2 in Ha. easy.
          rewrite H2 in Ha. easy.
        * rewrite H1 in H0.
          case_eq (beta (App t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc. rewrite !type_eqb_refl.
          cbn. easy.
          rewrite H2 in H0. easy.
        * cbn in Ha. easy.
        * cbn in Ha.
          rewrite H1 in H0.
          case_eq b; intros.
          + subst. inversion H0. rewrite <- H2. easy.
          + subst. inversion H0. rewrite <- H2. easy.
        * rewrite H1 in H0.
          case_eq (beta (ITE t t0 t4) ); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t5 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Fix t) ); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t0 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Plus t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Minus t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Mult t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Eq t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.
        * rewrite H1 in H0.
          case_eq (beta (Gt t t0)); intros.
          rewrite H2 in H0.
          inversion H0.
          rewrite H1 in IHt1.
          specialize (IHt1 t4 Bool Ha H2).
          cbn. rewrite IHt1.
          rewrite Hb, Hc.
          rewrite !type_eqb_refl. cbn. easy.
          rewrite H2 in H0. easy.

      - cbn in H0.
        case_eq t; intros.
        + rewrite H1 in H0.
          cbn in H0. inversion H0.
        + rewrite H1 in *.
          inversion H0.
          cbn in H.
          case_eq (typecheck (extend nil s t0) t1); intros.
          ++ rewrite H2 in H.
             case_eq (type_eqb t0 t2); intros.
             * rewrite H4 in H.
               inversion H.
               specialize (subst_preserves_typing s t1 (Fix (Lambda s t0 t1)) T t0 nil); intros.
               rewrite H5. easy.
               subst. easy.
               cbn. rewrite H2. 
               rewrite H4. 
               apply type_eqb_eq in H4. subst. easy.
             * rewrite H4 in H. easy.
          ++ rewrite H2 in H. easy.
        + rewrite H1 in *.
          case_eq ( beta (App t0 t1)); intros.
          rewrite H2 in H0.
          inversion H0. cbn.
          specialize (IHt t2 (Arrow T T)).
          rewrite IHt.
          rewrite type_eqb_refl. easy.
          apply fixTyping in H. easy.
          easy.
          rewrite H2 in H0. easy.
        + rewrite H1 in *. cbn in *. easy.
        + rewrite H1 in *. cbn in *. easy.
        + rewrite H1 in *.
          case_eq (beta (ITE t0 t1 t2)); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn. 
             specialize (IHt t3 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Fix t0)); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t1 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Plus t0 t1) ); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t2 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Minus t0 t1) ); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t2 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Mult t0 t1) ); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t2 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Eq t0 t1) ); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t2 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.
        + rewrite H1 in *.
          case_eq (beta (Gt t0 t1) ); intros.
          ++ rewrite H2 in H0.
             inversion H0.
             cbn.
             specialize (IHt t2 (Arrow T T)).
             rewrite IHt. rewrite type_eqb_refl. easy.
             apply fixTyping in H. easy.
             easy.
          ++ rewrite H2 in H0. easy.

(** (Plus t1 t2) *)

      - cbn in H.
        case_eq (typecheck nil t1); intros.
        + rewrite H1 in H. 
          destruct t.
          case_eq ( typecheck nil t2); intros.
          ++ rewrite H2 in H.
             destruct t; try easy.
             cbn in H0.
             case_eq t1; intros; rewrite H3 in H1; try easy.
             * cbn in H1.
               case_eq (typecheck (extend nil s t) t0); intros.
               rewrite H4 in H1. easy. 
               rewrite H4 in H1. easy.
             * rewrite H3 in H0.
               case_eq (beta (App t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1. rewrite H2. easy.
               subst. easy. subst. easy.
               rewrite H5 in H0. cbn in H0.
               inversion H0. cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq t2; intros; rewrite H4 in H2; try easy.
               ** cbn in H2. 
                  case_eq (typecheck (extend nil s t) t0); intros.
                  rewrite H5 in H2. easy.
                  rewrite H5 in H2. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  assert (Ha: isvalue (NVal n) = true) by easy.
                  rewrite Ha in H0.
                  case_eq (beta (App t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  inversion H0. cbn. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (ITE t t0 t3)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t4 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Fix t)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t0 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Plus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Minus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Mult t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Eq t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Gt t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (ITE t t0 t3)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t4 Int).
               specialize (IHt2 t5 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (ITE t t0 t3) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t4 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Fix t)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t0 Int).
               specialize (IHt2 t3 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Fix t) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t0 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Plus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Plus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Minus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Minus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Mult t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Mult t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Eq t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Eq t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Gt t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Gt t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
          ++ rewrite H2 in H. easy.
          ++ easy.
          ++ easy.
        + rewrite H1 in H. easy.
       


(** (Minus t1 t2) *)

      - cbn in H.
        case_eq (typecheck nil t1); intros.
        + rewrite H1 in H. 
          destruct t.
          case_eq ( typecheck nil t2); intros.
          ++ rewrite H2 in H.
             destruct t; try easy.
             cbn in H0.
             case_eq t1; intros; rewrite H3 in H1; try easy.
             * cbn in H1.
               case_eq (typecheck (extend nil s t) t0); intros.
               rewrite H4 in H1. easy. 
               rewrite H4 in H1. easy.
             * rewrite H3 in H0.
               case_eq (beta (App t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1. rewrite H2. easy.
               subst. easy. subst. easy.
               rewrite H5 in H0. cbn in H0.
               inversion H0. cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq t2; intros; rewrite H4 in H2; try easy.
               ** cbn in H2. 
                  case_eq (typecheck (extend nil s t) t0); intros.
                  rewrite H5 in H2. easy.
                  rewrite H5 in H2. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  assert (Ha: isvalue (NVal n) = true) by easy.
                  rewrite Ha in H0.
                  case_eq (beta (App t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  inversion H0. cbn. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (ITE t t0 t3)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t4 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Fix t)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t0 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Plus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Minus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Mult t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Eq t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Gt t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (ITE t t0 t3)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t4 Int).
               specialize (IHt2 t5 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (ITE t t0 t3) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t4 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Fix t)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t0 Int).
               specialize (IHt2 t3 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Fix t) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t0 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Plus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Plus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Minus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Minus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Mult t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Mult t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Eq t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Eq t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Gt t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Gt t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
          ++ rewrite H2 in H. easy.
          ++ easy.
          ++ easy.
        + rewrite H1 in H. easy.


(** (Mult t1 t2) *)

      - cbn in H.
        case_eq (typecheck nil t1); intros.
        + rewrite H1 in H. 
          destruct t.
          case_eq ( typecheck nil t2); intros.
          ++ rewrite H2 in H.
             destruct t; try easy.
             cbn in H0.
             case_eq t1; intros; rewrite H3 in H1; try easy.
             * cbn in H1.
               case_eq (typecheck (extend nil s t) t0); intros.
               rewrite H4 in H1. easy. 
               rewrite H4 in H1. easy.
             * rewrite H3 in H0.
               case_eq (beta (App t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1. rewrite H2. easy.
               subst. easy. subst. easy.
               rewrite H5 in H0. cbn in H0.
               inversion H0. cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq t2; intros; rewrite H4 in H2; try easy.
               ** cbn in H2. 
                  case_eq (typecheck (extend nil s t) t0); intros.
                  rewrite H5 in H2. easy.
                  rewrite H5 in H2. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  assert (Ha: isvalue (NVal n) = true) by easy.
                  rewrite Ha in H0.
                  case_eq (beta (App t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  inversion H0. cbn. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (ITE t t0 t3)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t4 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Fix t)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t0 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Plus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Minus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Mult t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Eq t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Gt t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (ITE t t0 t3)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t4 Int).
               specialize (IHt2 t5 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (ITE t t0 t3) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t4 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Fix t)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t0 Int).
               specialize (IHt2 t3 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Fix t) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t0 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Plus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Plus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Minus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Minus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Mult t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Mult t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Eq t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Eq t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Gt t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Gt t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
          ++ rewrite H2 in H. easy.
          ++ easy.
          ++ easy.
        + rewrite H1 in H. easy.


(** (Eq t1 t2) *)

      - cbn in H.
        case_eq (typecheck nil t1); intros.
        + rewrite H1 in H. 
          destruct t.
          case_eq ( typecheck nil t2); intros.
          ++ rewrite H2 in H.
             destruct t; try easy.
             cbn in H0.
             case_eq t1; intros; rewrite H3 in H1; try easy.
             * cbn in H1.
               case_eq (typecheck (extend nil s t) t0); intros.
               rewrite H4 in H1. easy. 
               rewrite H4 in H1. easy.
             * rewrite H3 in H0.
               case_eq (beta (App t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1. rewrite H2. easy.
               subst. easy. subst. easy.
               rewrite H5 in H0. cbn in H0.
               inversion H0. cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq t2; intros; rewrite H4 in H2; try easy.
               ** cbn in H2. 
                  case_eq (typecheck (extend nil s t) t0); intros.
                  rewrite H5 in H2. easy.
                  rewrite H5 in H2. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  assert (Ha: isvalue (NVal n) = true) by easy.
                  rewrite Ha in H0.
                  case_eq (beta (App t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  inversion H0. cbn. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (ITE t t0 t3)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t4 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Fix t)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t0 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Plus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Minus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Mult t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Eq t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Gt t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (ITE t t0 t3)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t4 Int).
               specialize (IHt2 t5 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (ITE t t0 t3) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t4 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Fix t)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t0 Int).
               specialize (IHt2 t3 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Fix t) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t0 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Plus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Plus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Minus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Minus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Mult t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Mult t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Eq t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Eq t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Gt t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Gt t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
          ++ rewrite H2 in H. easy.
          ++ easy.
          ++ easy.
        + rewrite H1 in H. easy.



(** (Gt t1 t2) *)


      - cbn in H.
        case_eq (typecheck nil t1); intros.
        + rewrite H1 in H. 
          destruct t.
          case_eq ( typecheck nil t2); intros.
          ++ rewrite H2 in H.
             destruct t; try easy.
             cbn in H0.
             case_eq t1; intros; rewrite H3 in H1; try easy.
             * cbn in H1.
               case_eq (typecheck (extend nil s t) t0); intros.
               rewrite H4 in H1. easy. 
               rewrite H4 in H1. easy.
             * rewrite H3 in H0.
               case_eq (beta (App t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1. rewrite H2. easy.
               subst. easy. subst. easy.
               rewrite H5 in H0. cbn in H0.
               inversion H0. cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq t2; intros; rewrite H4 in H2; try easy.
               ** cbn in H2. 
                  case_eq (typecheck (extend nil s t) t0); intros.
                  rewrite H5 in H2. easy.
                  rewrite H5 in H2. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  assert (Ha: isvalue (NVal n) = true) by easy.
                  rewrite Ha in H0.
                  case_eq (beta (App t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  inversion H0. cbn. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (ITE t t0 t3)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t4 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Fix t)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t0 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Plus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Minus t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Mult t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Eq t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
               ** rewrite H4 in H0.
                  assert (beta (NVal n) = None).
                  { easy. }
                  rewrite H5 in H0.
                  case_eq (beta (Gt t t0)); intros.
                  rewrite H6 in H0.
                  inversion H0. cbn.
                  rewrite H4 in *.
                  specialize (IHt2 t3 Int H2 H6).
                  rewrite IHt2. easy.
                  rewrite H6 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (ITE t t0 t3)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t4 Int).
               specialize (IHt2 t5 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (ITE t t0 t3) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t4 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Fix t)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t0 Int).
               specialize (IHt2 t3 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Fix t) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t0 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Plus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Plus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Minus t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Minus t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Mult t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Mult t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Eq t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Eq t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
             * rewrite H3 in H0.
               case_eq (beta (Gt t t0)); intros.
               rewrite H4 in H0.
               case_eq (beta t2); intros.
               rewrite H5 in H0.
               inversion H0. cbn.
               specialize (IHt1 t3 Int).
               specialize (IHt2 t4 Int).
               rewrite IHt1, H2.
               easy. subst. easy. subst. easy.
               rewrite H5 in H0.
               assert (Ha: isvalue (Gt t t0) = false) by easy.
               rewrite Ha in H0. inversion H0.
               cbn.
               rewrite <- H3 in H1.
               specialize (IHt1 t3 Int H1).
               rewrite IHt1, H2. easy.
               subst. easy.
               rewrite H4 in H0. easy.
          ++ rewrite H2 in H. easy.
          ++ easy.
          ++ easy.
        + rewrite H1 in H. easy.
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
         specialize (progressR x T H); intros.
         destruct H0. rewrite Hnv in H0. easy.
         destruct H0. exists x0. easy.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (preservation x y T H H0); intros.
         specialize (IHmulti H2).
         apply IHmulti. split; easy.
Qed.

Check progressR.

Theorem soundness_R: forall n t t' T, 
  typecheck nil t = Some T -> 
  evaln t n  = Some t' -> 
  ~ stuck_b t'.
Proof. intros n. unfold stuck_b.
       induction n; intros.
       - unfold not. intros (Hnf, Hnv).
         specialize (progressR t T H); intros.
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
         specialize (progressR t T H); intros.
         cbn in *. inversion H0.
       - unfold not. intros (Hnf, Hnv).
         unfold step in *.
         specialize (progressR t T H); intros.
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
         specialize (progressR x T H); intros.
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
