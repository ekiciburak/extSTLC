From SFL Require Import Imports Auxiliaries.

Require Import Coq.Strings.String.



Inductive type: Type :=
  | Int
  | Bool
  | Arrow: type -> type -> type.

Fixpoint type_eqb (t1 t2: type): bool :=
  match t1, t2 with
    | Int, Int => true
    | Bool, Bool => true
    | Arrow a1 a2, Arrow b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
    | _, _ => false
  end.

Lemma type_eqb_refl: forall t, type_eqb t t = true.
Proof. intro t.
       induction t; intros.
       - easy.
       - easy.
       - simpl. rewrite IHt1, IHt2. easy.
Qed.

Lemma type_eqb_eq: forall t1 t2, type_eqb t1 t2 = true -> t1 = t2.
Proof. intro t1.
       induction t1; intros.
       - cbn in *. case_eq t2; intros.
         easy. subst. easy. subst. easy.
       - cbn in *. case_eq t2; intros.
         subst. easy. easy. subst. easy.
       - cbn in *.
         case_eq t2; intros.
         subst. easy.
         subst. easy.
         subst. rewrite Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
Defined.

Lemma type_eqb_neq: forall t1 t2, type_eqb t1 t2 = false -> t1 <> t2.
Proof. intro t1.
       induction t1; intros.
       - cbn in *. case_eq t2; intros;
         rewrite H0 in H; easy.
       - cbn in *. case_eq t2; intros; try easy.
         rewrite H0 in H. easy.
       - cbn in *.
         case_eq t2; intros.
         subst. easy.
         subst. easy.
         subst. rewrite Bool.andb_false_iff in H.
         destruct H as [H1 | H2].
         + specialize (IHt1_1 _ H1). unfold not in *.
           intros. inversion H. easy.
         + specialize (IHt1_2 _ H2). unfold not in *.
           intros. inversion H. easy.
Defined.


Definition type_eqbO (t1 t2: option type): bool :=
  match t1, t2 with
    | Some t1, Some t2 => type_eqb t1 t2
    | None, None => true
    | _, _ => false
  end.

Lemma type_eqbO_refl: forall (t: option type),
  type_eqbO t t = true.
Proof. intro t.
       induction t; intros.
       - unfold type_eqbO.
         rewrite type_eqb_refl.
         easy.
       - easy.
Defined.

Lemma type_eqb0_eq: forall (t1 t2: option type),
  type_eqbO t1 t2 = true <-> t1 = t2.
Proof. intro t1.
       split.
       revert t2.
       induction t1; intros.
       + case_eq t2; intros.
         subst. simpl in *.
         apply type_eqb_eq in H. subst. easy.
         subst. cbn in *. easy.
       + cbn in *.
         case_eq t2; intros.
         subst. easy.
         easy.
       + intro H. subst.
         rewrite type_eqbO_refl. easy.
Qed.

Inductive term: Type :=
  | Ident : string -> term
  | Lambda: string -> type -> term -> term
  | App   : term   -> term -> term
  | NVal  : nat    -> term
  | BVal  : bool   -> term
  | ITE   : term   -> term -> term -> term
  | Fix   : term   -> term
  | Plus  : term   -> term -> term
  | Minus : term   -> term -> term
  | Mult  : term   -> term -> term
  | Eq    : term   -> term -> term
  | Gt    : term   -> term -> term.


Fixpoint isvalue (t: term): bool :=
  match t with
    | Lambda x t e => true
    | NVal n       => true
    | BVal b       => true
    | _            => false
  end.

Lemma isvalue_dec: forall t: term, isvalue t = true \/ isvalue t = false.
Proof. intro t.
       induction t; intros.
       - cbn. now right.
       - cbn. now left.
       - cbn. now right.
       - cbn. now left.
       - cbn. now left.
       - cbn. now right.
       - cbn. destruct IHt. now right. now right.
       - cbn. now right.
       - cbn. now right.
       - cbn. now right.
       - cbn. now right.
       - cbn. now right.
Qed.

Fixpoint term_eqb (t1 t2: term): bool :=
match t1, t2 with
  | Ident s, Ident t => if eqb s t then true else false
  | Lambda s1 t1 e1, Lambda s2 t2 e2 =>
      if type_eqb t1 t2 then 
        if eqb s1 s2 then term_eqb e1 e2
        else false
      else false
  | App e1 e2, App e3 e4 => term_eqb e1 e3 && term_eqb e2 e4
  | ITE e1 e2 e3, ITE e4 e5 e6 => term_eqb e1 e4 && term_eqb e2 e5 && 
                                  term_eqb e3 e6
  | Fix f1, Fix f2  => term_eqb f1 f2
  | NVal n, NVal m  => Nat.eqb n m
  | BVal a, BVal b  => Bool.eqb a b
  | Plus a1 b1, Plus a2 b2 => term_eqb a1 a2 && term_eqb b1 b2
  | Minus a1 b1, Minus a2 b2 => term_eqb a1 a2 && term_eqb b1 b2
  | Mult a1 b1, Mult a2 b2 => term_eqb a1 a2 && term_eqb b1 b2
  | Eq a1 b1, Eq a2 b2 => term_eqb a1 a2 && term_eqb b1 b2
  | Gt a1 b1, Gt a2 b2 => term_eqb a1 a2 && term_eqb b1 b2
  | _, _ => false
end.



Lemma term_eqb_refl: forall t, term_eqb t t = true.
Proof. intro t.
       induction t; intros.
       - cbn. now rewrite eqb_refl.
       - cbn. rewrite type_eqb_refl. cbn.
         rewrite eqb_refl. easy.
       - cbn in *. rewrite IHt1, IHt2. easy.
       - cbn. rewrite nat_eqb_refl. easy.
       - cbn. rewrite bool_eqb_refl. easy.
       - cbn. rewrite IHt1, IHt2, IHt3. easy.
       - cbn. rewrite IHt. easy.
       - cbn. rewrite IHt1, IHt2. easy.
       - cbn. rewrite IHt1, IHt2. easy.
       - cbn. rewrite IHt1, IHt2. easy.
       - cbn. rewrite IHt1, IHt2. easy.
       - cbn. rewrite IHt1, IHt2. easy.
Qed.

Lemma term_eqb_eq: forall t1 t2, term_eqb t1 t2 = true -> t1 = t2.
Proof. intro t1.
       induction t1; intros.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         subst. cbn in *. 
         case_eq (s =? s0); intros.
         + rewrite String.eqb_eq in H0. subst. easy.
         + rewrite H0 in H. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         subst. cbn in *.
         case_eq (type_eqb t t0 ); intros.
         + rewrite H0 in H.
           case_eq (s =? s0 ); intros.
           ++ rewrite H1 in H.
              rewrite String.eqb_eq in H1.
              apply type_eqb_eq in H0.
              specialize (IHt1 _ H).
              subst. easy.
           ++ rewrite H1 in H. cbn in H. easy.
         + rewrite H0 in H. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         cbn in *. rewrite H0 in H.
         rewrite Bool.andb_true_iff in H.
         destruct H as (Ha, Hb).
         specialize (IHt1_1 _ Ha).
         specialize (IHt1_2 _ Hb).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply nat_eqb_eq in H.
         rewrite H. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply bool_eqb_eq in H.
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         cbn in H.
         rewrite H0 in H.
         rewrite !Bool.andb_true_iff in H.
         destruct H as ((Ha, Hb), Hc).
         specialize (IHt1_1 _ Ha).
         specialize (IHt1_2 _ Hb).
         specialize (IHt1_3 _ Hc).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         specialize (IHt1 _ H).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
       - case_eq t2; intros; try (subst; cbn in *; easy).
         rewrite H0 in H.
         cbn in H.
         apply Bool.andb_true_iff in H.
         destruct H as (H1, H2).
         specialize (IHt1_1 _ H1).
         specialize (IHt1_2 _ H2).
         subst. easy.
Qed.

Fixpoint term_eqbO (t1 t2: option term): bool :=
  match t1, t2 with
    | Some t1, Some t2 => term_eqb t1 t2
    | None, None => true
    | _, _ => false
  end.

Lemma term_eqbO_refl: forall t: option term,
  term_eqbO t t = true.
Proof. intros.
       case_eq t; intros.
       - cbn. rewrite term_eqb_refl. easy.
       - easy.
Defined.


Lemma term_eqbO_eq: forall t1 t2: option term,
  term_eqbO t1 t2 = true -> t1 = t2.
Proof. intro t1.
       induction t1; intros.
       - cbn in H. case_eq t2; intros.
         + rewrite H0 in H.
           apply term_eqb_eq in H.
           subst. easy.
         + rewrite H0 in H. easy.
       - cbn in *. case_eq t2; intros.
         + rewrite H0 in H. easy.
         + easy.
Qed.

Fixpoint fv_e (e: term) (l: list string): list string :=
  match e with
    | Ident s         => s :: l
    | Lambda x t e1   => List.filter (fun a => negb (eqb a x)) (fv_e e1 l)
    | Fix f           => fv_e f l
    | App t r         => unique (fv_e t l ++ fv_e r l)
    | ITE t1 t2 t3    => unique (fv_e t1 l ++ fv_e t2 l ++ fv_e t3 l)
    | Plus t1 t2      => unique (fv_e t1 l ++ fv_e t2 l)
    | Minus t1 t2     => unique (fv_e t1 l ++ fv_e t2 l)
    | Mult t1 t2      => unique (fv_e t1 l ++ fv_e t2 l)
    | Eq t1 t2        => unique (fv_e t1 l ++ fv_e t2 l)
    | Gt t1 t2        => unique (fv_e t1 l ++ fv_e t2 l)
    | _               => l
  end.

Definition fv (e: term) := fv_e e nil.

Lemma In0: forall (x: string) (t: term) (T: type),
 not (List.In x (fv (Lambda x T t))).
Proof. intros.
       unfold not. intros.
       cbn in H. rewrite List.filter_In in H.
       destruct H.
       rewrite String.eqb_refl in H0.
       easy.
Qed.

Fixpoint subst (e: term) (x: string) (n: term): term :=
  match e with
    | Ident s      => if String.eqb s x then n else e
    | Lambda y t m => if (Bool.eqb (String.eqb y x) false)
                      then Lambda y t (subst m x n) 
                      else e
    | Fix f        => Fix (subst f x n)
    | App t r      => App (subst t x n) (subst r x n)
    | ITE t1 t2 t3 => ITE (subst t1 x n) (subst t2 x n) (subst t3 x n)
    | Plus a b     => Plus (subst a x n) (subst b x n)
    | Minus a b    => Minus (subst a x n) (subst b x n)
    | Mult a b     => Mult (subst a x n) (subst b x n)
    | Eq a b       => Eq (subst a x n) (subst b x n)
    | Gt a b       => Gt (subst a x n) (subst b x n)
    | _            => e
  end.

Lemma find0: forall t x s T, 
  find x (fv t) = true -> 
  (s =? x) = false ->
  find x (fv (Lambda s T t)) = true.
Proof. intros.
       apply In1 in H.
       apply In1.
       cbn in *.
       apply List.filter_In.
       split.
       + easy.
       + rewrite String.eqb_sym. rewrite H0. easy.
Qed.

Lemma uh_diff: forall l x a b,
List.In x (unique_help l a) ->
(x =? b) = false ->
List.In x (unique_help l b).
Proof. intro l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in *.
         case_eq (a0 =? a); intros.
         case_eq (b =? a ); intros.
         rewrite H1 in H.
         rewrite String.eqb_eq in H1, H2. subst. easy.
         rewrite H1 in H. cbn.
         specialize (IHl x a0 b H H0). now right.
         rewrite H1 in H. cbn in H. destruct H.
         subst. rewrite String.eqb_sym in H0.
         rewrite H0. cbn. now left.
         case_eq (b =? a); intros.
         apply (IHl x a0 b). easy. easy.
         cbn. right.
         apply (IHl x a0 b). easy. easy.
Qed.



Lemma not_uh: forall l x a,
  ~ List.In x l ->
  ~ List.In x (unique_help l a).
Proof. intro l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in *. unfold not in *. intros.
         apply (IHl x a). intros.
         apply H. now right.
         case_eq ( a0 =? a ); intros.
         + rewrite H1 in H0.
           rewrite String.eqb_eq in H1. subst. easy.
         + rewrite H1 in H0. cbn in *.
           destruct H0. subst. destruct H. now left.
           case_eq ((x =? a)); intros.
           * rewrite String.eqb_eq in H2.
             destruct H. now left.
           * specialize (uh_diff l x a0 a H0 H2); intros. easy.
Qed.


Lemma listU: forall l x,
 List.In x (unique l) -> List.In x l.
Proof. intro l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in *. destruct H.
         + now left.
         + right. apply IHl.
           specialize (@List.in_dec string string_dec x l); intros.
           destruct H0. apply In5 in i. easy.
           specialize (IHl x).
           assert (~ List.In x l -> ~List.In x (unique l)).
           { unfold not. intros.
             apply H0. apply IHl. easy. }
           specialize (H0 n).
           specialize (not_uh (unique l) x a H0); intros.
           easy.
Qed.

Lemma uh_drop: forall l x a,
List.In x (unique_help l a) ->
List.In x l.
Proof. intro l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in *.
         case_eq (a0 =? a ); intros.
         + rewrite H0 in H.
           rewrite String.eqb_eq in H0. subst.
           specialize (IHl _ _ H). now right.
         + rewrite H0 in H. cbn in H. destruct H.
           now left.
           specialize (IHl x a0 H). now right.
Qed.

Lemma listE: forall l m x,
  List.In x (unique (l ++ m)) ->
  List.In x l \/ List.In x m.
Proof. intro l.
       induction l; intros.
       - cbn in *. right.
         apply listU in H. easy.
       - cbn in *.
         destruct H. left. now left.
         rewrite unique_h_comm in H.
         apply listU in H.
         rewrite unique_help0 in H.
         apply List.in_app_or in H.
         case_eq ((x =? a)); intros.
         + rewrite String.eqb_eq in H0. left. now left.
         + destruct H.
           apply uh_drop in H. left. now right.
           apply uh_drop in H. now right.
Qed.
