From SFL Require Import Imports Terms Auxiliaries Typecheck.
Require Import Coq.Strings.String.

Definition gtb (n m: nat): bool := Nat.ltb m n.

Fixpoint beta (e: term): option term :=
  match e with
    | Ident s                    => None
    | Lambda x t e               => None
    | NVal n                     => None
    | BVal b                     => None
    | (Fix (Lambda x t e1)) as f => Some (subst e1 x f)
    | Fix f                      => let bf := beta f in
                                    match bf with
                                      | Some sbf => Some (Fix sbf)
                                      | None     => None
                                    end
    | App (Lambda x t e1) e2     => if isvalue e2 then Some (subst e1 x e2) 
                                    else
                                      let e2' := beta e2 in
                                      match e2' with
                                        | Some e2'' => Some (App (Lambda x t e1) e2'')
                                        | None      => None
                                      end
    | App e1 e2                  => if isvalue e1 then
                                      let e2' := beta e2 in 
                                      match e2' with
                                        | Some e2'' => Some (App e1 e2'')
                                        | None      => None
                                      end
                                    else
                                      let e1' := beta e1 in 
                                      match e1' with 
                                        | Some e1'' => Some (App e1'' e2)
                                        | None      => None
                                      end
    | ITE (BVal true) e2 e3      => Some e2
    | ITE (BVal false) e2 e3     => Some e3
    | ITE e1 e2 e3               => let e1' := beta e1 in
                                    match e1' with
                                      | Some e1''   => Some (ITE e1'' e2 e3)
                                      | None        => None
                                    end
    | Plus (NVal n) (NVal m)     => Some (NVal (n + m))
    | Plus a b                   => if isvalue a then 
                                      let b' := beta b in
                                      match b' with
                                        | Some b'' => Some (Plus a b'')
                                        | None     => None
                                      end
                                     else
                                      let a' := beta a in
                                      match a' with
                                        | Some a'' => Some (Plus a'' b)
                                        | None     => None
                                      end
    | Minus (NVal n) (NVal m)    => Some (NVal (n - m))
    | Minus a b                  => if isvalue a then 
                                      let b' := beta b in
                                      match b' with
                                        | Some b'' => Some (Minus a b'')
                                        | None     => None
                                      end
                                     else
                                      let a' := beta a in
                                      match a' with
                                        | Some a'' => Some (Minus a'' b)
                                        | None     => None
                                      end
    | Mult (NVal n) (NVal m)     => Some (NVal (n * m))
    | Mult  a b                  => if isvalue a then 
                                      let b' := beta b in
                                      match b' with
                                        | Some b'' => Some (Mult a b'')
                                        | None     => None
                                      end
                                     else
                                      let a' := beta a in
                                      match a' with
                                        | Some a'' => Some (Mult a'' b)
                                        | None     => None
                                      end
    | Eq (NVal n) (NVal m)       => Some (BVal (Nat.eqb n m))
    | Eq a b                     => if isvalue a then 
                                      let b' := beta b in
                                      match b' with
                                        | Some b'' => Some (Eq a b'')
                                        | None     => None
                                      end
                                     else
                                      let a' := beta a in
                                      match a' with
                                        | Some a'' => Some (Eq a'' b)
                                        | None     => None
                                      end
    | Gt (NVal n) (NVal m)       => Some (BVal (gtb n m))
    | Gt a b                     => if isvalue a then 
                                      let b' := beta b in
                                      match b' with
                                        | Some b'' => Some (Gt a b'')
                                        | None     => None
                                      end
                                     else
                                      let a' := beta a in
                                      match a' with
                                        | Some a'' => Some (Gt a'' b)
                                        | None     => None
                                      end
  end.

Lemma isvalue_beta: forall t: term, isvalue t = true -> beta t = None.
Proof. intro t; induction t; intros; easy. Qed.

Definition factorial := 
                Lambda "f" (Arrow Int (Arrow Int Int)) 
                 (Lambda "x" Int 
                   (Lambda "y" Int
                   (ITE (Gt (Ident "x") (NVal 1)) 
                        (Plus (Mult (Ident "x") (App (App (Ident "f") (Minus (Ident "x") (NVal 1))) (Ident "y"))) (Ident "y"))
                        (NVal 1))) 
                  ).

Definition f := App (App (Fix factorial) (NVal 7)) (NVal 2).

Fixpoint evaln (t: term) (n: nat): option term :=
  match n with
    | O   => Some t
    | S n => let t' := beta t in
             match t' with
               | Some t' => evaln t' n
               | None    => None
             end
  end.

Eval compute in evaln f 53.

Eval compute in evaln (App (NVal 5) (ITE (NVal 3) (NVal 5) (NVal 10))) 1.





