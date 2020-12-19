
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


  (** http://color.inria.fr/papers/koprowski06draft.pdf -- look into "Theorem autoType" *)

Lemma typecheck_decidable: forall t c, exists T, typecheck c t = Some T \/ typecheck c t = None.
Proof. intro t.
       induction t; intros.
       - cbn. induction c; intros.
         + cbn. exists Int. now right.
         + cbn. destruct a.
           case_eq (s0 =? s); intros; destruct IHc as (T, th).
           ++ exists t. now left.
           ++ exists T. easy.
       - cbn. specialize (IHt (extend c s t)).
         destruct IHt as (T, IHt).
         exists (Arrow t T). destruct IHt as [ IHt | IHt].
         ++ rewrite IHt. now left.
         ++ rewrite IHt. now right.
       - cbn. specialize (IHt1 c).
         destruct IHt1 as (T, IHt1).
         destruct IHt1 as [ IHt1 | IHt1 ].
         + rewrite IHt1.
           destruct T; intros.
           ++ exists Int. now right.
           ++ exists Bool. now right.
           ++ exists T2.
              specialize (IHt2 c).
              destruct IHt2 as (T, IHt2).
              destruct IHt2 as [IHt2 | IHt2 ].
              +++ rewrite IHt2.
                  case_eq (type_eqb T1 T); intros.
                  * now left.
                  * now right.
              +++ rewrite IHt2. now right.
         + rewrite IHt1. exists Int. now right.
       - cbn. exists Int. now left.
       - cbn. exists Bool. now left.
       - cbn. specialize (IHt1 c).
         destruct IHt1 as (T, IHt1).
         destruct IHt1 as [IHt1 | IHt1 ].
         + rewrite IHt1.
           specialize (IHt2 c).
           destruct IHt2 as (T2, IHt2).
           destruct IHt2 as [ IHt2 | IHt2 ].
           rewrite IHt2.
           specialize (IHt3 c).
           destruct IHt3 as (T3, IHt3).
           destruct IHt3 as [ IHt3 | IHt3 ].
           rewrite IHt3.
           exists T2.
           case_eq T; intros.
           ++ cbn. now right.
           ++ cbn. case_eq (type_eqb T2 T3); intros.
              +++ now left.
              +++ now right.
           ++ cbn. now right.
           ++ rewrite IHt3. exists T. now right.
           ++ rewrite IHt2. exists T. now right.
         + rewrite IHt1. exists T. now right.
       - cbn. specialize (IHt c).
         destruct IHt as (T, IHt).
         destruct IHt as [ IHt | IHt ].
         rewrite IHt.
         case_eq T; intros.
         + exists T. now right.
         + exists T. now right.
         + exists t1. 
           case_eq (type_eqb t0 t1); intros. now left. now right.
         + exists T. rewrite IHt. now right.
       - cbn.
         specialize (IHt1 c).
         specialize (IHt2 c).
         destruct IHt1 as (ty1, IHt1).
         destruct IHt2 as (ty2, IHt2).
         destruct IHt1 as [ IHt1 | IHt1 ]; 
         destruct IHt2 as [ IHt2 | IHt2 ].
         + rewrite IHt1, IHt2.
           destruct ty1; destruct ty2; try (exists Int; now right).
           exists Int. now left.
         + rewrite IHt1, IHt2.
           destruct ty1; exists Int; now right.
         + rewrite IHt1. exists Int. now right.
         + rewrite IHt1. exists Int. now right.
       - cbn.
         specialize (IHt1 c).
         specialize (IHt2 c).
         destruct IHt1 as (ty1, IHt1).
         destruct IHt2 as (ty2, IHt2).
         destruct IHt1 as [ IHt1 | IHt1 ]; 
         destruct IHt2 as [ IHt2 | IHt2 ].
         + rewrite IHt1, IHt2.
           destruct ty1; destruct ty2; try (exists Int; now right).
           exists Int. now left.
         + rewrite IHt1, IHt2.
           destruct ty1; exists Int; now right.
         + rewrite IHt1. exists Int. now right.
         + rewrite IHt1. exists Int. now right.
       - cbn.
         specialize (IHt1 c).
         specialize (IHt2 c).
         destruct IHt1 as (ty1, IHt1).
         destruct IHt2 as (ty2, IHt2).
         destruct IHt1 as [ IHt1 | IHt1 ]; 
         destruct IHt2 as [ IHt2 | IHt2 ].
         + rewrite IHt1, IHt2.
           destruct ty1; destruct ty2; try (exists Int; now right).
           exists Int. now left.
         + rewrite IHt1, IHt2.
           destruct ty1; exists Int; now right.
         + rewrite IHt1. exists Int. now right.
         + rewrite IHt1. exists Int. now right.
       - cbn.
         specialize (IHt1 c).
         specialize (IHt2 c).
         destruct IHt1 as (ty1, IHt1).
         destruct IHt2 as (ty2, IHt2).
         destruct IHt1 as [ IHt1 | IHt1 ]; 
         destruct IHt2 as [ IHt2 | IHt2 ].
         + rewrite IHt1, IHt2.
           destruct ty1; destruct ty2; try (exists Bool; now right).
           exists Bool. now left.
         + rewrite IHt1, IHt2.
           destruct ty1; exists Bool; now right.
         + rewrite IHt1. exists Bool. now right.
         + rewrite IHt1. exists Bool. now right. 
       - cbn.
         specialize (IHt1 c).
         specialize (IHt2 c).
         destruct IHt1 as (ty1, IHt1).
         destruct IHt2 as (ty2, IHt2).
         destruct IHt1 as [ IHt1 | IHt1 ]; 
         destruct IHt2 as [ IHt2 | IHt2 ].
         + rewrite IHt1, IHt2.
           destruct ty1; destruct ty2; try (exists Bool; now right).
           exists Bool. now left.
         + rewrite IHt1, IHt2.
           destruct ty1; exists Bool; now right.
         + rewrite IHt1. exists Bool. now right.
         + rewrite IHt1. exists Bool. now right. 
Qed.


Definition istypechecked (c: ctx) (t: term): bool :=
  let ty := typecheck c t in
  match ty with
    | Some ty' => true
    | None     => false
  end. 


Lemma istypechecked_t1: forall (t1 t2: term), istypechecked nil (App t1 t2) = true ->
  istypechecked nil t1 = true.
Proof. intro t1.
       case_eq t1; intros.
       - cbn in *. easy.
       - unfold istypechecked in *.
         case_eq (typecheck nil (Lambda s t t0)); intros.
         easy.
         cbn in *.
         case_eq (typecheck (extend nil s t) t0); intros.
         + rewrite H2 in H0, H1. easy.
         + rewrite H2 in H0. easy.
       - unfold istypechecked in *.
         case_eq (typecheck nil (App t t0)); intros.
         easy.
         case_eq (typecheck nil (App (App t t0) t2)); intros.
         rewrite H2 in H0. cbn in *.
         case_eq (typecheck nil t); intros.
         + rewrite H3 in H2, H1.
           case_eq t4; intros.
           * subst. easy.
           * subst. easy.
           * subst. case_eq (typecheck nil t0); intros.
             rewrite H in *. cbn in *.
             case_eq (type_eqb t5 t1); intros.
             rewrite H4 in *. easy.
             rewrite H4 in *. easy.
             rewrite H in *. easy.
         + rewrite H3 in *. easy.
         + rewrite H2 in *. easy.
       - cbn. easy.
       - cbn. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (typecheck nil t); intros.
         rewrite H1 in *.
         case_eq (typecheck nil t0 ); intros.
         rewrite H2 in *.
         case_eq (typecheck nil t2); intros.
         rewrite H3 in *.
         case_eq (type_eqb t4 Bool && type_eqb t5 t6); intros.
         rewrite H4 in *. easy.
         rewrite H4 in *.
         easy. 
         rewrite H3 in *. easy.
         rewrite H2 in *. easy.
         rewrite H1 in *. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (typecheck nil t ); intros.
         rewrite H1 in H0.
         case_eq (match t0 with
                    | Arrow t1 t2 => if type_eqb t1 t2 then Some t2 else None
                    | _ => None
                  end); intros. easy.
         rewrite H2 in H0. easy.
         rewrite H1 in H0. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                   | Some Int => Some Int
                                   | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                   | Some Int => Some Int
                                   | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                   | Some Int => Some Int
                                   | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                   | Some Int => Some Bool
                                   | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                   | Some Int => Some Bool
                                   | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0. easy.
Qed.

Lemma istypechecked_t2: forall (t1 t2: term), istypechecked nil (App t1 t2) = true ->
  istypechecked nil t2 = true.
Proof. intros t1 t2. 
       revert t1.
       case_eq t2; intros.
       - cbn in *. 
         unfold istypechecked in *. cbn in *.
         case_eq (typecheck nil t1); intros.
         rewrite H1 in *.
         case_eq t; intros.
         rewrite H2 in *. easy.
         rewrite H2 in *. easy.
         rewrite H2 in *. easy.
         rewrite H1 in *. easy.
       - unfold istypechecked in *.
         case_eq (typecheck nil (Lambda s t t0)); intros.
         easy.
         cbn in *.
         case_eq (typecheck (extend nil s t) t0); intros.
         + rewrite H2 in H0, H1. easy.
         + rewrite H2 in H1. 
           case_eq (typecheck nil t1 ); intros.
           rewrite H3 in *.
           case_eq t3; intros.
           rewrite H4 in *. easy.
           rewrite H4 in *. easy.
           rewrite H4, H2 in *. easy.
           rewrite H3 in *. easy.
       - unfold istypechecked in *.
         case_eq (typecheck nil (App t t0)); intros.
         easy. cbn in *.
         case_eq (typecheck nil t1); intros.
         rewrite H2 in *.
         case_eq t3; intros.
         rewrite H3 in *.
         easy.
         rewrite H3 in *.
         easy. 
         rewrite H3 in *.
         case_eq (typecheck nil t); intros.
         rewrite H4 in *.
         case_eq t6; intros. 
         rewrite H5 in *. easy.
         rewrite H5 in *. easy.
         rewrite H5 in *.
         case_eq (typecheck nil t0 ); intros.
         rewrite H6 in *.
         case_eq (type_eqb t7 t9); intros.
         rewrite H7 in *.
         easy.
         rewrite H7 in *. easy.
         rewrite H6 in *. easy.
         rewrite H4 in *. easy.
         rewrite H2 in *. easy.
       - easy.
       - easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (typecheck nil t3); intros.
         rewrite H1 in *.
         case_eq (t4 ); intros.
         rewrite H2 in *. easy.
         rewrite H2 in *. easy.
         rewrite H2 in *.
         case_eq (typecheck nil t); intros.
         rewrite H3 in *.
         case_eq (typecheck nil t0); intros.
         rewrite H4 in *.
         case_eq (typecheck nil t1); intros.
         rewrite H5 in *.
         case_eq (type_eqb t7 Bool && type_eqb t8 t9); intros.
         rewrite H6 in *. easy.
         rewrite H6 in *. easy.
         rewrite H5 in *. easy.
         rewrite H4 in *. easy.
         rewrite H3 in *. easy.
         rewrite H1 in *. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (typecheck nil t); intros.
         rewrite H1 in H0.
         case_eq t0; intros; subst.
         case_eq (typecheck nil t1); intros; rewrite H in H0.
         destruct t0; intros; easy.
         easy.
         case_eq (typecheck nil t1); intros; rewrite H in H0.
         destruct t0; intros; easy.
         easy.
         case_eq (type_eqb t3 t4); intros. easy.
         rewrite H in H0.
         destruct (typecheck nil t1).
         destruct t0; easy. easy.
         rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t0; intros; easy.
         easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                    | Some Int => Some Int
                                    | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t3; intros; easy. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                    | Some Int => Some Int
                                    | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t3; intros; easy. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                    | Some Int => Some Int
                                    | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t3; intros; easy. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                    | Some Int => Some Bool
                                    | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t3; intros; easy. easy.
       - unfold istypechecked in *.
         cbn in *.
         case_eq (match typecheck nil t with
                    | Some Int => match typecheck nil t0 with
                                    | Some Int => Some Bool
                                    | _ => None
                                  end
                    | _ => None
                  end); intros. easy. rewrite H1 in H0.
         case_eq (typecheck nil t1); intros; rewrite H2 in H0.
         destruct t3; intros; easy. easy.
Qed.


Lemma istypechecked_ite1: forall (t1 t2 t3: term), istypechecked nil (ITE t1 t2 t3) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true /\ istypechecked nil t3 = true.
Proof. intro t1.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t1); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros.
       rewrite  H1 in H0.
       case_eq (typecheck nil t3); intros.
       split; easy. split. easy.
       rewrite H2 in H0. easy.
       rewrite H1 in H0. easy. 
Qed.

Lemma istypechecked_ite2: forall (t1 t2 t3: term) T, typecheck nil (ITE t1 t2 t3) = Some T ->
  typecheck nil t1 = Some Bool /\ typecheck nil t2 = Some T /\ typecheck nil t3 = Some T.
Proof. intro t1.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t1); intros; try easy.
       case_eq (typecheck nil t2); intros.
       rewrite  H1 in H0.
       case_eq (typecheck nil t3); intros.
       rewrite H2 in H0.
       case_eq (type_eqb t Bool && type_eqb t0 t4); intros.
       rewrite H3 in H0. inversion H0.
       apply Bool.andb_true_iff in H3.
       destruct H3 as (Ha, Hb).
       apply type_eqb_eq in Ha.
       apply type_eqb_eq in Hb.
       subst. split;easy.
       rewrite H3 in H0. easy.
       rewrite H2 in H0. easy.
       rewrite H1 in H0. easy. 
Qed.

Lemma istypechecked_st: forall (t: term), istypechecked nil (Fix t) = true ->
  istypechecked nil t = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; easy.
Qed.

Lemma istypechecked_plus: forall (t1 t2: term), istypechecked nil (Plus t1 t2) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros. easy.
       rewrite  H1 in H0.
       destruct t0; easy.
Qed.


Lemma istypechecked_plus2: forall (t1 t2: term), istypechecked nil (Plus t1 t2) = true ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       case_eq (typecheck nil t2); intros.
       rewrite  H1 in H0.
       destruct t0; destruct t1; easy.
       rewrite H1 in H0. 
       destruct t0; easy.
Qed.


Lemma istypechecked_minus: forall (t1 t2: term), istypechecked nil (Minus t1 t2) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros. easy.
       rewrite  H1 in H0.
       destruct t0; easy.
Qed.

Lemma istypechecked_mult: forall (t1 t2: term), istypechecked nil (Mult t1 t2) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros. easy.
       rewrite  H1 in H0.
       destruct t0; easy.
Qed.

Lemma istypechecked_eq: forall (t1 t2: term), istypechecked nil (Eq t1 t2) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros. easy.
       rewrite  H1 in H0.
       destruct t0; easy.
Qed.


Lemma istypechecked_eq2: forall (t1 t2: term), istypechecked nil (Eq t1 t2) = true ->
  typecheck nil t1 = Some Int /\ typecheck nil t2 = Some Int.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       case_eq (typecheck nil t2); intros.
       rewrite  H1 in H0.
       destruct t0; destruct t1; easy.
       rewrite H1 in H0. 
       destruct t0; easy.
Qed.

Lemma istypechecked_gt: forall (t1 t2: term), istypechecked nil (Gt t1 t2) = true ->
  istypechecked nil t1 = true /\ istypechecked nil t2 = true.
Proof. intro t.
       unfold istypechecked. cbn.
       case_eq (typecheck nil t); intros; try easy.
       split. easy.
       case_eq (typecheck nil t2); intros. easy.
       rewrite  H1 in H0.
       destruct t0; easy.
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
         + apply H0. apply find0; easy.
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

Lemma subst0: forall t v x T, 
(subst (Lambda x T t) x v) = (Lambda x T t).
Proof. intros.
       induction t; intros; simpl; rewrite String.eqb_refl; simpl; easy.
Qed.

(* Lemma subst00: forall t v x T f T2, 
(subst (Fix f x T t T2) x v) = (Fix f x T t T2).
Proof. intros.
       induction t; intros; simpl; rewrite String.eqb_refl; simpl; easy.
Qed. *)


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

(* Lemma fv_neq0: forall t x y T f T2,
  find y (fv (Fix f x T t T2)) = true -> String.eqb x y = false /\ String.eqb f y = false.
Proof. intros.
       apply In1 in H. cbn in H.
       apply List.filter_In in H.
       destruct H.
       apply Bool.andb_true_iff in H0. 
       destruct H0.
       case_eq ((y =? x)); intros.
       + rewrite H2 in H0. cbn in H0. easy.
       + rewrite String.eqb_sym in H2. rewrite H2. 
         case_eq (f =? y); intros.
         ++ rewrite String.eqb_sym in H1.
            rewrite H3 in H1. easy.
         ++ easy.
Qed. *)

Lemma cinv0: forall t x s T T2 U G,
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

Lemma cinv1: forall a b A B C t T G,
  String.eqb a b = false ->
  typecheck ((a, A) :: (b, B) :: (b, C) :: G) t = Some T ->
  typecheck ((a, A) :: (b, B) :: G) t = Some T.
Proof. intros.
       specialize (context_invariance ((a, A) :: (b, B) :: (b, C) :: G) ((a, A) :: (b, B) :: G) t T H0); intros.
       rewrite H1. easy.
       intros y Hy. cbn.
       case_eq (a =? y); intros. easy.
       case_eq (b =? y); intros. easy. easy.
Qed.


Lemma cinv2: forall a b c A B C t T G,
  String.eqb a b = false ->
  String.eqb b c = false ->
  String.eqb a c = false ->
  typecheck ((a, A) :: (b, B) :: (c, C) :: G) t = Some T ->
  typecheck ((c, C) :: (a, A) :: (b, B) :: G) t = Some T.
Proof. intros.
       specialize (context_invariance ((a, A) :: (b, B) :: (c, C) :: G) 
                                      ((c, C) :: (a, A) :: (b, B) :: G) t T H2); intros.
       rewrite H3. easy.
       intros y Hy. cbn.
       case_eq (a =? y); intros.
       apply String.eqb_eq in H4.
       subst. rewrite String.eqb_sym in H1.
       rewrite H1. easy.
       case_eq (b =? y); intros.
       apply String.eqb_eq in H5.
       subst. rewrite String.eqb_sym in H0.
       rewrite H0. easy.
       case_eq (c =? y); intros.
       easy. easy.
Qed.
