(** * Check : QuickChick on Constraint-based 0-CFA  *)
From CFA Require Export Analyse.
From CFA Require Export Ordered.
From CFA Require Export Ancilla.
From CFA Require Export Constraints.

(** ** Generate Expressions  *)

Import ListNotations.
Fixpoint max_elt (nl : list nat) : nat :=
  match nl with
  | nil => 0
  | n' :: nl' => max n' (max_elt nl')
  end.

Definition fresh (nl : list nat) : nat := S (max_elt nl).
Definition nat_to_var (n : nat) :=
  Strings.String.string_of_list_ascii [(Strings.Ascii.ascii_of_nat n)].
Definition fresh_var (nl : list nat) : var * list nat :=
  let n := fresh nl in (nat_to_var n, n :: nl).


From QuickChick Require Import QuickChick. Import QcNotation.
Export MonadNotation. Open Scope monad_scope.

Derive (Arbitrary, Show) for cst.
Derive (Arbitrary, Show) for op.
Derive Show for fon_p.

(** Here we write a generator for fon_p where type is not considered.
    In other words, the checker would not type-check but only the 
    0-CFA analysis results. *)
Fixpoint gen_exp_sized (size : nat) (vars : list nat) (env : list string) :
  G (option fon_p) :=
  let range := (0%nat, 20%nat) in
  let rec size' vars env :=
      [ (* fon_p_cst c *)
        (size, ret (fon_p_cst (c_Z (Z.of_nat (fresh vars))))) ;
      (* fun_p_id x *)
      (size, ret (fon_p_id (fst (fresh_var vars)))) ;
      (* fon_p_fun x e *)
      (size, let (x, vars) := fresh_var vars in
             e <- gen_exp_sized size' vars (x :: env) ;;
             ret (fon_p_fun x e)) ;
      (* fon_p_fix f x e *)
      (size, let (f, vars) := fresh_var vars in
             let (x, vars) := fresh_var vars in
             e <- gen_exp_sized size' vars (x :: (f :: env)) ;;
             ret (fon_p_fix f x e)) ;
      (* fon_p_app e1 e2 *)
      (size, e1 <- gen_exp_sized size' vars env ;;
             e2 <- gen_exp_sized size' vars env ;;
             ret (fon_p_app e1 e2)) ;
      (* fon_p_if e1 e2 e3 *)
      (size, e1 <- gen_exp_sized size' vars env ;;
             e2 <- gen_exp_sized size' vars env ;;
             e3 <- gen_exp_sized size' vars env ;;
             ret (fon_p_if e1 e2 e3)) ;
      (* fon_p_let x e1 e2 *)
      (size, let (x, vars) := fresh_var vars in
             e1 <- gen_exp_sized size' vars env ;;
             e2 <- gen_exp_sized size' vars (x :: env) ;;
             ret (fon_p_let x e1 e2)) ;
      (* fon_p_op op e1 e2 *)
      (size, e1 <- gen_exp_sized size' vars env ;;
             e2 <- gen_exp_sized size' vars env ;;
             (* the type of operator doesn't matter *)
             ret (fon_p_op op__plus e1 e2)) 
      ]
  in
  match size with
  | 0 => backtrack [(1, (ret (fon_p_cst (c_Z (Z.of_nat (fresh vars))))))]
  | S size' => backtrack (rec size' [] [])
  end.

Definition check_acceptable :=
  let size := 2%nat in
  forAll (gen_exp_sized size [] [])
         (fun me =>
            match me with
            | Some e =>
              let tl := (label_fon_p e) in
              let (ch, eh) := O_CFA tl in
              analyse_s ch eh tl
            | None => false
            end).

(** Call QuickChick on our 0-CFA analysis :  *)
(* QuickChick check_acceptable. *)

(** Due to some implementation details as well as potential mistakes
    in function definitions, the QuickChick shows failure, which is
    not evident when we simply encode the example (λx. x) (λy. y) earlier! *)
