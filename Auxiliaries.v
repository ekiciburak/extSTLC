

From SFL Require Import Imports.
Require Import Coq.Strings.String.


Fixpoint find (elem: string) (l: list string) :=
match l with
  | nil => false
  | x :: xs => if eqb elem x then true else find elem xs
end.

Fixpoint unique_help l n :=
match l with
  | nil    => nil
  | h :: t => if eqb n h then unique_help t n else h::(unique_help t n)
end.

Fixpoint unique x :=
match x with
  | nil   => nil
  | h::t => h::(unique_help (unique t) h)
end.


Lemma unique_help0: forall l m a,
unique_help (l ++ m) a = List.app (unique_help l a) (unique_help m a).
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn. rewrite IHl.
         case_eq ( a0 =? a ); intros.
         + easy.
         + cbn. easy.
Qed.


Lemma nat_eqb_refl: forall n: nat, Nat.eqb n n = true.
Proof. intro n.
       induction n; intros.
       - cbn. easy.
       - cbn. exact IHn.
Qed.

Lemma bool_eqb_refl: forall n: bool, Bool.eqb n n = true.
Proof. intro n.
       induction n; intros.
       - cbn. easy.
       - cbn. easy.
Qed.

Lemma nat_eqb_eq: forall (n m: nat), Nat.eqb n m = true -> n = m.
Proof. intro n.
       induction n; intros.
       - case_eq m; intros.
         + easy.
         + subst. easy.
       - case_eq m; intros.
         + subst. easy.
         + f_equal. apply IHn.
           subst. inversion H. easy.
Qed.

Lemma bool_eqb_eq: forall (n m: bool), Bool.eqb n m = true -> n = m.
Proof. intro n.
       induction n; intros.
       - cbn in H.
         case_eq m; intros; subst; easy.
       - cbn in H.
         case_eq m; intros; subst; easy.
Qed.

Lemma unique_h0: forall l a x,
(x =? a) = false ->
unique_help (unique_help l a) x = unique_help (unique_help l x) a.
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn. case_eq (a0 =? a ); intros.
         + rewrite String.eqb_eq in H0.
           subst. rewrite H. rewrite IHl. cbn.
           rewrite String.eqb_refl. easy.
           easy.
         + case_eq (x =? a); intros.
           ++ cbn. rewrite H1. rewrite IHl. easy.
               easy.
           ++ cbn. rewrite H1, H0.
              rewrite IHl. easy. easy.
Qed.

Lemma unique_h1: forall l a,
unique_help (unique_help l a) a = (unique_help l a).
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn. case_eq (a0 =? a); intros.
         + rewrite String.eqb_eq in H.
           subst. rewrite !IHl. easy.
         + cbn. rewrite H. rewrite IHl. easy.
Qed.

Lemma unique_h_comm: forall l x,
unique_help (unique l) x = unique (unique_help l x).
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn. case_eq ( x =? a ); intros.
         + rewrite String.eqb_eq in H.
           rewrite H.
           rewrite unique_h1.
           rewrite IHl. easy.
         + cbn. rewrite unique_h0.
           rewrite IHl. easy.
           easy.
Qed.


Lemma In1: forall l x, List.In x l <-> find x l = true.
Proof. split. 
       - intro H.
         revert x H.
         induction l; intros.
         + cbn in *. easy.
         + cbn in *. destruct H.
           ++ rewrite H. now rewrite String.eqb_refl.
           ++ case_eq (x =? a); intros.
              +++ easy.
              +++ apply IHl. easy.
       - revert x. 
         induction l; intros.
         + cbn in *. easy.
         + cbn in *.
           case_eq (x =? a); intros.
           ++ rewrite String.eqb_eq in H0.
              left. easy.
           ++ right.
              rewrite H0 in H. 
              apply IHl. easy.
Qed.

Lemma In2: forall l x, not (List.In x l) <-> find x l = false.
Proof. split. 
       - intro H.
         revert x H.
         induction l; intros.
         + cbn in *. easy.
         + cbn in *. unfold not in H.
           case_eq (x =? a); intros.
           ++ rewrite String.eqb_eq in H0.
              symmetry in H0.
              assert (a = x \/ List.In x l).
              { now left. }
              specialize (H H1). easy.
           ++ apply IHl. unfold not. intros.
              assert (a = x \/ List.In x l).
              { now right. }
              specialize (H H2). easy.
       - unfold not.
         revert x.
         induction l; intros.
         + cbn in *. easy.
         + cbn in *.
           case_eq (x =? a); intros.
           ++ rewrite H1 in H. easy.
           ++ rewrite H1 in H.
              destruct H0 as [H0 | H0].
              +++ rewrite H0 in H1.
                  rewrite String.eqb_refl in H1. easy.
              +++ apply (IHl x); easy.
Qed.



Lemma In3: forall l a,
not (List.In a l) -> (unique_help l a) = l.
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn in *. unfold not in *.
         case_eq (a0 =? a); intros.
         + rewrite String.eqb_eq in H0.
           assert ( a = a0 \/ List.In a0 l) by now left.
           now specialize (H H1).
         + f_equal. apply IHl.
           intros. apply H.
           now right.
Qed.


Lemma In4: forall l a x,
String.eqb a x = false ->
List.In x l ->
List.In a l ->
List.In x (unique_help l a).
Proof. intro l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in *.
         destruct H0; destruct H1.
         + subst. rewrite String.eqb_refl in H. easy.
         + subst. rewrite H. cbn. now left.
         + subst. 
           specialize (@List.in_dec string string_dec a0 l); intros.
           destruct H1.
           ++ rewrite String.eqb_refl. apply IHl; easy.
           ++ rewrite String.eqb_refl. 
              rewrite In3; easy.
         + case_eq (a0 =? a); intros.
           ++ apply IHl; easy.
           ++ cbn. right. apply IHl; easy.
Qed.

Lemma In5: forall l x,
List.In x l ->
List.In x (unique l).
Proof. intro l.
       induction l; intros.
       - simpl in *. easy.
       - cbn in H. destruct H.
         + now left.
         + cbn.
           case_eq (String.eqb a x); intros.
           ++ rewrite String.eqb_eq in H0. now left.
           ++ specialize (@List.in_dec string string_dec a (unique l)); intros.
              destruct H1.
              +++ right. apply In4.
                  easy. apply IHl. easy. easy.
              +++ right. rewrite In3. apply IHl. easy. easy.
Qed.

Lemma In6: forall (l m: list string) x,
List.In x l ->
List.In x (l ++ m).
Proof. intros.
       apply List.in_or_app.
       now left.
Qed.


Lemma In7: forall (l m: list string) x,
List.In x m ->
List.In x (l ++ m).
Proof. intros.
       apply List.in_or_app.
       now right.
Qed.


Lemma In8: forall (l: list string) (x y: string),
   find x l = true ->
   find y l = false -> eqb x y = false.
Proof. intros l.
       induction l; intros.
       - cbn in *. easy.
       - cbn in H, H0.
         case_eq (y =? a); intros.
         + rewrite H1 in H0. easy.
         + rewrite H1 in H0.
           case_eq (x =? a); intros.
           ++ apply String.eqb_eq in H2.
              subst. rewrite String.eqb_sym. easy.
           ++ rewrite H2 in H.
              apply IHl; easy.
Qed.



