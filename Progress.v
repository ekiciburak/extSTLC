From SFL Require Import Imports Terms Auxiliaries Typecheck Eval.
Require Import Coq.Strings.String.



(* typed small-step semantics -- typed reduction steps *)
Definition typed_beta (l: ctx) (e: term): option term :=
  let te := typecheck l e in
  match te with 
    | Some te => beta e
    | None    => None
  end.

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

(******************)

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

Definition typecheck_op (t: term) :=
  let te := beta t in
  match te with
    | Some t' => typecheck nil t'
    | None    => None
  end.


(* Lemma progress: forall t,
  istypechecked nil t  = true ->
  (isvalue t = true) \/ (exists t', term_eqbO (beta t) (Some t') = true).
Proof. intros t Htc.
       induction t; intros.
       - right. cbn in *. easy.
       - cbn. now left.
       - right.
         assert (Htt1: istypechecked nil t1 = true).
         { apply istypechecked_t1 in Htc. easy. }
         specialize (IHt1 Htt1).
         assert (Htt2: istypechecked nil t2 = true).
         { apply istypechecked_t2 in Htc. easy. }
         specialize (IHt2 Htt2).
         destruct IHt1 as [ IHt1 | IHt1 ].
         + destruct IHt2 as [ IHt2 | IHt2 ].
           ++ case_eq t1; intros.
              * subst. easy.
              * cbn. rewrite IHt2. exists ((subst t0 s t2)).
                now rewrite term_eqbO_refl.
              * subst. cbn in *. easy.
              * cbn. rewrite H in Htc. cbn in Htc. easy.
              * cbn. rewrite H in Htc. cbn in Htc. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
           ++ *)



Lemma progress: forall t,
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
           ++ case_eq t1; intros.
              * subst. easy.
              * cbn. rewrite it2. exists ((subst t0 s t2)).
                now rewrite term_eqbO_refl.
              * subst. cbn in *. easy.
              * cbn. rewrite H in Htc. cbn in Htc. easy.
              * cbn. rewrite H in Htc. cbn in Htc. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *. easy.
           ++ assert (Htt2: istypechecked nil t2 = true).
              { apply istypechecked_t2 in Htc. easy. }
              specialize (IHt2 Htt2).
              destruct IHt2 as [it2' | Hstep].
              +++ rewrite it2 in it2'. easy.
              +++ destruct Hstep as (t', Hstep).
                  exists (App t1 t'). cbn.
                  case_eq t1; intros.
                  * subst. easy.
                  * rewrite it2.
                    case_eq (beta t2 ); intros. cbn in *.
                    rewrite type_eqb_refl.
                    rewrite String.eqb_refl.
                    rewrite H0 in Hstep.
                    inversion Hstep.
                    rewrite H2.
                    now rewrite term_eqb_refl.
                    rewrite H0 in Hstep. cbn in *. easy.
                 * subst. easy.
                 * cbn. subst. easy.
                 * cbn. subst. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
                 * subst. cbn in *. easy.
         + assert (Htt1: istypechecked nil t1 = true).
           { apply istypechecked_t1 in Htc. easy. }
           specialize (IHt1 Htt1).
           destruct IHt1 as [IHt1 | IHt1].
           ++ rewrite it1 in IHt1. easy.
           ++ destruct IHt1 as (t', Hstep). 
              exists (App t' t2). cbn.
              case_eq t1; intros.
              * subst. cbn in *. inversion Hstep.
              * subst. cbn in *. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. easy.
              * subst. cbn in *. easy.
              * subst. cbn in *.
                case_eq (match t with
                            | BVal true => Some t0
                            | BVal false => Some t3
                            | _ => match beta t with
                                     | Some e1'' => Some (ITE e1'' t0 t3)
                                     | None => None
                                   end
                         end); intros. rewrite H in Hstep.
               apply term_eqbO_eq in Hstep.
               inversion Hstep.
               rewrite term_eqbO_refl. easy.
               rewrite H in Hstep. easy.
              * subst. cbn in *.
                apply term_eqbO_eq in Hstep. rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
              * subst. rewrite it1.
                apply term_eqbO_eq in Hstep.
                rewrite Hstep.
                rewrite term_eqbO_refl. easy.
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
         case_eq t1; intros.
         + subst. easy.
         + subst. contradict Ha. cbn.
           case_eq (typecheck (extend nil s t0) t4); easy.
         + subst. easy.
         + subst. cbn in Ha.  easy.
         + cbn. case_eq b; intros.
           exists t2. rewrite term_eqbO_refl. easy.
           exists t3. rewrite term_eqbO_refl. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst. cbn in *. easy.
         + subst.
           destruct Hstep as (T, Hstep).
           apply term_eqbO_eq in Hstep.
           cbn.
           rewrite Hstep.
           case_eq t1; intros; try (exists ((ITE T t2 t3)); rewrite term_eqbO_refl; easy).
           case_eq b; intros.
           exists t2. rewrite term_eqbO_refl; easy.
           exists t3. rewrite term_eqbO_refl; easy.
         + intros. rewrite H in Htc. easy.
       - pose proof Htc as Htc0.
         apply istypechecked_st in Htc.
         specialize (IHt Htc).
         destruct IHt as [ IHt | IHt ].
         + cbn. right.
           pose proof IHt as HH.
           apply isvalue_beta in IHt.
           rewrite IHt.
           destruct t; cbn in HH; try easy. cbn.
           exists ((subst t0 s (Fix (Lambda s t t0)))).
           rewrite term_eqb_refl. easy.
         + destruct IHt as (tt, IHt).
           right. cbn.
           apply term_eqbO_eq in IHt.
           rewrite IHt.
           destruct t; try (exists (Fix tt); rewrite term_eqbO_refl; easy).
           * exists ((subst t0 s (Fix (Lambda s t t0)))).
             rewrite term_eqbO_refl. easy.
       - pose proof Htc as Htc0.
         specialize (isvalue_dec t1); intros it1.
         + right.
           apply istypechecked_plus2 in Htc0.
           destruct Htc0 as (Ha, Hb).
           unfold istypechecked in IHt1, IHt2.
           rewrite Ha in IHt1.
           rewrite Hb in IHt2.
           specialize (IHt1 eq_refl).
           specialize (IHt2 eq_refl).
           cbn.
           destruct it1 as [it1 | it1];
           pose proof it1 as it1'.
           ++ case_eq t1; intros; rewrite H in it1; cbn in it1; try easy.
              +++ rewrite H in Ha. cbn in Ha.
                  case_eq (typecheck (extend nil s t) t0); intros;
                  rewrite H0 in Ha; easy.
              +++ destruct IHt2 as [IHt2 | IHt2].
                  case_eq t2; intros; try (rewrite H0 in IHt2; cbn in IHt2; easy).
                  * rewrite H0 in Hb. cbn in Hb.
                    case_eq (typecheck (extend nil s t) t0); intros;
                    rewrite H1 in Hb; easy.
                  * exists (NVal (n + n0)).
                    rewrite term_eqbO_refl. easy.
                  * rewrite H0 in Hb. easy.
                  * destruct IHt2 as (t, Hstep).
                    apply term_eqbO_eq in Hstep.
                    rewrite Hstep. cbn.
                    case_eq t2; try (exists (Plus (NVal n) t); rewrite term_eqbO_refl; easy).
                    intros m H1.
                    rewrite H1 in Hstep. cbn in Hstep. easy.
              +++ cbn. rewrite H in Ha. easy.
           ++ destruct IHt1 as [IHt1 | IHt1].
              rewrite it1 in IHt1. easy.
              destruct IHt1 as (t, Hstep).
              apply term_eqbO_eq in Hstep.
              rewrite Hstep, it1.
              case_eq t1; try (exists (Plus t t2); rewrite term_eqbO_refl; easy).
              intros n H0.
              subst. easy.
       - pose proof Htc as Htc0.
         right.
         apply istypechecked_minus in Htc.
         destruct Htc as (H1, H2).
         specialize (IHt1 H1).
         specialize (IHt2 H2).
         destruct IHt1 as [ IHt1 | IHt1 ];
         destruct IHt2 as [ IHt2 | IHt2 ].
         pose proof IHt1 as HH1.
         pose proof IHt2 as HH2.
         + apply isvalue_beta in IHt1.
           cbn.
           rewrite IHt1.
           rewrite HH1.
           apply isvalue_beta in IHt2.
           rewrite IHt2.
           case_eq t1; intros; rewrite H in HH1; try easy.
           ++ subst. unfold istypechecked in Htc0, H1.
              case_eq (typecheck nil (Minus (Lambda s t t0) t2)); intros.
              +++ cbn in H. cbn in H1.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H0 in *. easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in Htc0. easy.
           ++ case_eq t2; intros; rewrite H0 in HH2; try easy.
              +++ subst. unfold istypechecked in Htc0, H2.
                  cbn in Htc0, H2.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H in *. easy.
                  ++++ rewrite H in *. easy.
              +++ exists (NVal (n - n0)). 
                  rewrite term_eqbO_refl. easy.
                  +++ subst. unfold istypechecked in *.
                      cbn in *. easy.
           ++ subst. unfold istypechecked in *.
              cbn in *. easy.
         + cbn. rewrite IHt1.
           destruct IHt2 as (t, IHt2).
           apply term_eqbO_eq in IHt2.
           rewrite IHt2.
           exists (Minus t1 t); destruct t1; try rewrite term_eqbO_refl; try easy.
           destruct t2; try (rewrite term_eqbO_refl; easy). cbn in *. easy.
         + case_eq t2; intros.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              unfold istypechecked in *.
              cbn in *.
              case_eq (typecheck (extend nil s t) t0); intros.
              +++ rewrite H in *.
                  case_eq (typecheck nil t1); intros.
                  ++++ rewrite H0 in *.
                       destruct t3; easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              destruct IHt1 as (t, IHt1).
              apply term_eqbO_eq in IHt1.
              rewrite IHt1.
              destruct t1.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (App t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Fix t1) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Minus t (NVal n)).
                  rewrite term_eqbO_refl. easy.
           ++ subst. unfold istypechecked in H1, Htc0. cbn in Htc0.
              case_eq (typecheck nil t1); intros.
              +++ rewrite H in *. destruct t; easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy.
         + destruct IHt1 as (ta, IHt1).
           destruct IHt2 as (tb, IHt2).
           apply term_eqbO_eq in IHt1.
           apply term_eqbO_eq in IHt2.
           cbn. rewrite IHt1, IHt2.
           destruct t1.
           ++ assert (isvalue (Ident s) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Lambda s t t1) = true) by easy.
              rewrite H.
              exists ((Minus (Lambda s t t1) tb)). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (App t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ destruct t2.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ exists (NVal (n - n0)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Minus (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (BVal b) = true) by easy.
              rewrite H.
              exists (Minus (BVal b) tb). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Fix t1) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Minus ta t2). rewrite term_eqbO_refl. easy.
       - pose proof Htc as Htc0.
         right.
         apply istypechecked_mult in Htc.
         destruct Htc as (H1, H2).
         specialize (IHt1 H1).
         specialize (IHt2 H2).
         destruct IHt1 as [ IHt1 | IHt1 ];
         destruct IHt2 as [ IHt2 | IHt2 ].
         pose proof IHt1 as HH1.
         pose proof IHt2 as HH2.
         + apply isvalue_beta in IHt1.
           cbn.
           rewrite IHt1.
           rewrite HH1.
           apply isvalue_beta in IHt2.
           rewrite IHt2.
           case_eq t1; intros; rewrite H in HH1; try easy.
           ++ subst. unfold istypechecked in Htc0, H1.
              case_eq (typecheck nil (Mult (Lambda s t t0) t2)); intros.
              +++ cbn in H. cbn in H1.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H0 in *. easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in Htc0. easy.
           ++ case_eq t2; intros; rewrite H0 in HH2; try easy.
              +++ subst. unfold istypechecked in Htc0, H2.
                  cbn in Htc0, H2.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H in *. easy.
                  ++++ rewrite H in *. easy.
              +++ exists (NVal (n * n0)). 
                  rewrite term_eqbO_refl. easy.
                  +++ subst. unfold istypechecked in *.
                      cbn in *. easy.
           ++ subst. unfold istypechecked in *.
              cbn in *. easy.
         + cbn. rewrite IHt1.
           destruct IHt2 as (t, IHt2).
           apply term_eqbO_eq in IHt2.
           rewrite IHt2.
           exists (Mult t1 t); destruct t1; try rewrite term_eqbO_refl; try easy.
           destruct t2; try (rewrite term_eqbO_refl; easy). cbn in *. easy.
         + case_eq t2; intros.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              unfold istypechecked in *.
              cbn in *.
              case_eq (typecheck (extend nil s t) t0); intros.
              +++ rewrite H in *.
                  case_eq (typecheck nil t1); intros.
                  ++++ rewrite H0 in *.
                       destruct t3; easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              destruct IHt1 as (t, IHt1).
              apply term_eqbO_eq in IHt1.
              rewrite IHt1.
              destruct t1.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (App t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Fix t1) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Mult t (NVal n)).
                  rewrite term_eqbO_refl. easy.
           ++ subst. unfold istypechecked in H1, Htc0. cbn in Htc0.
              case_eq (typecheck nil t1); intros.
              +++ rewrite H in *. destruct t; easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy.
         + destruct IHt1 as (ta, IHt1).
           destruct IHt2 as (tb, IHt2).
           apply term_eqbO_eq in IHt1.
           apply term_eqbO_eq in IHt2.
           cbn. rewrite IHt1, IHt2.
           destruct t1.
           ++ assert (isvalue (Ident s) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Lambda s t t1) = true) by easy.
              rewrite H.
              exists ((Mult (Lambda s t t1) tb)). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (App t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ destruct t2.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ exists (NVal (n * n0)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Mult (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (BVal b) = true) by easy.
              rewrite H.
              exists (Mult (BVal b) tb). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Fix t1) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Mult ta t2). rewrite term_eqbO_refl. easy.
       - pose proof Htc as Htc0.
         right.
         apply istypechecked_eq in Htc.
         destruct Htc as (H1, H2).
         specialize (IHt1 H1).
         specialize (IHt2 H2).
         destruct IHt1 as [ IHt1 | IHt1 ];
         destruct IHt2 as [ IHt2 | IHt2 ].
         pose proof IHt1 as HH1.
         pose proof IHt2 as HH2.
         + apply isvalue_beta in IHt1.
           cbn.
           rewrite IHt1.
           rewrite HH1.
           apply isvalue_beta in IHt2.
           rewrite IHt2.
           case_eq t1; intros; rewrite H in HH1; try easy.
           ++ subst. unfold istypechecked in Htc0, H1.
              case_eq (typecheck nil (Eq (Lambda s t t0) t2)); intros.
              +++ cbn in H. cbn in H1.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H0 in *. easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in Htc0. easy.
           ++ case_eq t2; intros; rewrite H0 in HH2; try easy.
              +++ subst. unfold istypechecked in Htc0, H2.
                  cbn in Htc0, H2.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H in *. easy.
                  ++++ rewrite H in *. easy.
              +++ exists (BVal (Nat.eqb n n0)). 
                  rewrite term_eqbO_refl. easy.
                  +++ subst. unfold istypechecked in *.
                      cbn in *. easy.
           ++ subst. unfold istypechecked in *.
              cbn in *. easy.
         + cbn. rewrite IHt1.
           destruct IHt2 as (t, IHt2).
           apply term_eqbO_eq in IHt2.
           rewrite IHt2.
           exists (Eq t1 t); destruct t1; try rewrite term_eqbO_refl; try easy.
           destruct t2; try (rewrite term_eqbO_refl; easy). cbn in *. easy.
         + case_eq t2; intros.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              unfold istypechecked in *.
              cbn in *.
              case_eq (typecheck (extend nil s t) t0); intros.
              +++ rewrite H in *.
                  case_eq (typecheck nil t1); intros.
                  ++++ rewrite H0 in *.
                       destruct t3; easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              destruct IHt1 as (t, IHt1).
              apply term_eqbO_eq in IHt1.
              rewrite IHt1.
              destruct t1.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (App t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Fix t1) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Eq t (NVal n)).
                  rewrite term_eqbO_refl. easy.
           ++ subst. unfold istypechecked in H1, Htc0. cbn in Htc0.
              case_eq (typecheck nil t1); intros.
              +++ rewrite H in *. destruct t; easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy.
         + destruct IHt1 as (ta, IHt1).
           destruct IHt2 as (tb, IHt2).
           apply term_eqbO_eq in IHt1.
           apply term_eqbO_eq in IHt2.
           cbn. rewrite IHt1, IHt2.
           destruct t1.
           ++ assert (isvalue (Ident s) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Lambda s t t1) = true) by easy.
              rewrite H.
              exists ((Eq (Lambda s t t1) tb)). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (App t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ destruct t2.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ exists (BVal (Nat.eqb n n0)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Eq (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (BVal b) = true) by easy.
              rewrite H.
              exists (Eq (BVal b) tb). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Fix t1) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Eq ta t2). rewrite term_eqbO_refl. easy.
       - pose proof Htc as Htc0.
         right.
         apply istypechecked_gt in Htc.
         destruct Htc as (H1, H2).
         specialize (IHt1 H1).
         specialize (IHt2 H2).
         destruct IHt1 as [ IHt1 | IHt1 ];
         destruct IHt2 as [ IHt2 | IHt2 ].
         pose proof IHt1 as HH1.
         pose proof IHt2 as HH2.
         + apply isvalue_beta in IHt1.
           cbn.
           rewrite IHt1.
           rewrite HH1.
           apply isvalue_beta in IHt2.
           rewrite IHt2.
           case_eq t1; intros; rewrite H in HH1; try easy.
           ++ subst. unfold istypechecked in Htc0, H1.
              case_eq (typecheck nil (Gt (Lambda s t t0) t2)); intros.
              +++ cbn in H. cbn in H1.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H0 in *. easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in Htc0. easy.
           ++ case_eq t2; intros; rewrite H0 in HH2; try easy.
              +++ subst. unfold istypechecked in Htc0, H2.
                  cbn in Htc0, H2.
                  case_eq (typecheck (extend nil s t) t0); intros.
                  ++++ rewrite H in *. easy.
                  ++++ rewrite H in *. easy.
              +++ destruct n.
                  ++++ exists (BVal false).
                       rewrite term_eqbO_refl. easy.
                  ++++ exists (BVal (Nat.leb n0 n)). 
                       rewrite term_eqbO_refl. easy.
                  +++ subst. unfold istypechecked in *.
                      cbn in *. easy.
           ++ subst. unfold istypechecked in *.
              cbn in *. easy.
         + cbn. rewrite IHt1.
           destruct IHt2 as (t, IHt2).
           apply term_eqbO_eq in IHt2.
           rewrite IHt2.
           exists (Gt t1 t); destruct t1; try rewrite term_eqbO_refl; try easy.
           destruct t2; try (rewrite term_eqbO_refl; easy). cbn in *. easy.
         + case_eq t2; intros.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              unfold istypechecked in *.
              cbn in *.
              case_eq (typecheck (extend nil s t) t0); intros.
              +++ rewrite H in *.
                  case_eq (typecheck nil t1); intros.
                  ++++ rewrite H0 in *.
                       destruct t3; easy.
                  ++++ rewrite H0 in *. easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in *. easy.
           ++ subst. cbn in *.
              destruct IHt1 as (t, IHt1).
              apply term_eqbO_eq in IHt1.
              rewrite IHt1.
              destruct t1.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (App t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ cbn in *. easy. 
              +++ cbn in *. easy. 
              +++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Fix t1) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
                  rewrite H. exists (Gt t (NVal n)).
                  rewrite term_eqbO_refl. easy.
           ++ subst. unfold istypechecked in H1, Htc0. cbn in Htc0.
              case_eq (typecheck nil t1); intros.
              +++ rewrite H in *. destruct t; easy.
              +++ rewrite H in *. easy.
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy. 
           ++ subst. cbn in IHt2. easy.
         + destruct IHt1 as (ta, IHt1).
           destruct IHt2 as (tb, IHt2).
           apply term_eqbO_eq in IHt1.
           apply term_eqbO_eq in IHt2.
           cbn. rewrite IHt1, IHt2.
           destruct t1.
           ++ assert (isvalue (Ident s) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Lambda s t t1) = true) by easy.
              rewrite H.
              exists ((Gt (Lambda s t t1) tb)). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (App t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ destruct t2.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ destruct n.
                  ++++ exists (BVal false).
                       rewrite term_eqbO_refl. easy.
                  ++++ exists (BVal (Nat.leb n0 n)).
                       rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
              +++ assert (isvalue (NVal n) = true) by easy.
                  rewrite H. exists (Gt (NVal n) tb).
                  rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (BVal b) = true) by easy.
              rewrite H.
              exists (Gt (BVal b) tb). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (ITE t1_1 t1_2 t1_3) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Fix t1) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Plus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Minus t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Mult t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Eq t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
           ++ assert (isvalue (Gt t1_1 t1_2) = false) by easy.
              rewrite H.
              exists (Gt ta t2). rewrite term_eqbO_refl. easy.
Qed.


Lemma progressR: forall t T,
  typecheck nil t  = Some T ->
  (isvalue t = true) \/ (exists t', beta t = Some t').
Proof. intros t T Htc.
       specialize (progress t); intros.
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
