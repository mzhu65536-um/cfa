(** * Language : Syntactic Forms of Lambda Calculus *)

From CFA Require Import Coqlib.

Definition var : Type := string.
Definition label : Type := Z.


Inductive cst : Type :=
| c_Z : Z -> cst
| c_bool : bool -> cst
(* | c_string : string -> cst *)
.

Inductive op : Type :=
| op__plus : op
| op__minus : op
| op__mult : op
| op__equal : op
.

(** ** the FONCTION Language (λ) *)

(* Pure fon_ (λ_p)*)
Inductive fon_p : Type :=
| fon_p_app : fon_p -> fon_p -> fon_p
| fon_p_fun : var -> fon_p -> fon_p
| fon_p_fix : var -> var -> fon_p -> fon_p
| fon_p_cst : cst -> fon_p
| fon_p_id : var -> fon_p
| fon_p_if : fon_p -> fon_p -> fon_p -> fon_p
| fon_p_op : op -> fon_p -> fon_p -> fon_p
| fon_p_let : var -> fon_p -> fon_p -> fon_p
.

(* Abstract fon_ (λ) *)
Inductive fon_ : Type :=
| fon__app : fon_l -> fon_l -> fon_
| fon__fun : var -> fon_l -> fon_
| fon__fix : var -> var -> fon_l -> fon_
| fon__cst : cst -> fon_
| fon__id : var -> fon_
| fon__if : fon_l -> fon_l -> fon_l -> fon_
| fon__op : op -> fon_l -> fon_l -> fon_
| fon__let : var -> fon_l -> fon_l -> fon_
(* label extension (λ_l) *)
with fon_l : Type :=
| lab : fon_ -> Z -> fon_l
.

(** Transform the pure FON language into the labeled one : *)
Fixpoint label_fon_p_aux (t : fon_p) (n : Z) : fon_l * Z :=
  match t with
  | fon_p_app t1 t2 =>
    let (tl1, n') := label_fon_p_aux t1 n in
    let (tl2, n'') := label_fon_p_aux t2 n' in
    (lab (fon__app tl1 tl2) n'', (Z.add 1 n''))
  | fon_p_let x t1 t2 =>
    let (tl1, n') := label_fon_p_aux t1 n in
    let (tl2, n'') := label_fon_p_aux t2 n' in
    (lab (fon__let x tl1 tl2) n'', (Z.add 1 n''))
  | fon_p_fun x t =>
    let (tl, n') := label_fon_p_aux t n in
    (lab (fon__fun x tl) n', (Z.add 1 n'))
  | fon_p_fix f x t =>
    let (tl, n') := label_fon_p_aux t n in
    (lab (fon__fix f x tl) n', (Z.add 1 n'))
  | fon_p_cst c =>
    (lab (fon__cst c) n, (Z.add 1 n))
  | fon_p_id x =>
    (lab (fon__id x) n, (Z.add 1 n))
  | fon_p_if t1 t2 t3 =>
    let (tl1, n') := label_fon_p_aux t1 n in
    let (tl2, n'') := label_fon_p_aux t2 n' in
    let (tl3, n''') := label_fon_p_aux t3 n'' in
    (lab (fon__if tl1 tl2 tl3) n''', (Z.add 1 n'''))
  | fon_p_op op t1 t2 =>
    let (tl1, n') := label_fon_p_aux t1 n in
    let (tl2, n'') := label_fon_p_aux t2 n' in
    (lab (fon__op op tl1 tl2) n'', (Z.add 1 n''))
  end.

Definition label_fon_p (t : fon_p) :  fon_l :=
  let (tl, n) := label_fon_p_aux t 1 in tl.

Definition x := "x"%string.
Definition y := "y"%string.
Definition z := "z"%string.
Definition f := "f"%string.
Definition g := "g"%string.

(** Check functionality of label_fon_p : *)
Definition example_exp1 : fon_p :=
  fon_p_app (fon_p_fun x (fon_p_id x)) (fon_p_fun y (fon_p_id y)).
Compute (label_fon_p example_exp1).

Definition example_exp2 : fon_p :=
  fon_p_let g
   (fon_p_fix f x (fon_p_app (fon_p_id f) (fon_p_fun y (fon_p_id y))))
   (fon_p_app (fon_p_id g) (fon_p_fun z (fon_p_id z))).
Compute (label_fon_p example_exp2).

Definition lab_of tl : Z :=
  match tl with
  | lab _ n => n
  end.


(** ** Intermezzo: the Intermediaire FONCTION language (iλ) *)
(** Before we start to list and prove properties on the analysis, let's first 
    meaning to our [fon_] language by defining the meaning of the language by 
    following the track in [PoPA], step into the abstract machine language 
    [ifon_].


    (FIXME: There might be a better way in terms of structual semantics
    of [fon_] , but let's first follow the track.)  
*)

Inductive ifon_ : Type :=
| ifon__app : ifon_l -> ifon_l -> ifon_
| ifon__fun : var -> fon_l -> ifon_
| ifon__fix : var -> var -> fon_l -> ifon_
| ifon__cst : cst -> ifon_
| ifon__id : var -> ifon_
| ifon__if : ifon_l -> ifon_l -> ifon_l -> ifon_
| ifon__op : op -> ifon_l -> ifon_l -> ifon_
| ifon__let : var -> ifon_l -> ifon_l -> ifon_
(** bind environment to new iλ *)
| ifon__bnd : env -> ifon_l -> ifon_
(** transform abstract into closure (abstract still lives in fonl)  *)
| ifon__cls : fon_ -> env -> ifon_
with ifon_l : Type := 
| ilab : ifon_ -> Z -> ifon_l
with ival : Type :=
| iv_cls : fon_ -> env -> ival
| iv_cst : cst -> ival
with env : Type :=
| empty_env 
| extend_env (x : var) (ival : ival) (e : env) 
.

(** There is a drawback for this implementation that [env] is now a mutually
    inductive type so that we cannot use built in Coq libraries.

    The following part is inspired by Compcert Maps Module
 *)
Fixpoint get_env (x : var) (e : env) : option ival :=
  match e with
  | empty_env => None
  | extend_env y itl e => if (String.eqb x y) then Some itl else get_env x e
  end.

Theorem gss (x : var) (itl : ival) (e : env) :
  get_env x (extend_env x itl e) = Some itl.
Proof with auto. unfold get_env. rewrite String.eqb_refl... Qed.

Theorem gso (x y : var) (itl : ival) (e : env) :
  x <> y -> get_env x (extend_env y itl e) = get_env x e.
Proof with auto.
  unfold get_env. intros. apply eqb_neq in H. rewrite H...
Qed.

Fixpoint inj (tl : fon_l) : ifon_l :=
  match tl with
  | lab t l =>
    match t with
    | fon__app e1 e2 => ilab (ifon__app (inj e1) (inj e2)) l
    | fon__fun x e => ilab (ifon__fun x e) l
    | fon__fix f x e => ilab (ifon__fix f x e) l
    | fon__cst c => ilab (ifon__cst c) l
    | fon__id x => ilab (ifon__id x) l
    | fon__if e1 e2 e3 => ilab (ifon__if (inj e1) (inj e2) (inj e3)) l
    | fon__op op e1 e2 => ilab (ifon__op op (inj e1) (inj e2)) l
    | fon__let x e1 e2 => ilab (ifon__let x (inj e1) (inj e2)) l
    end
  end.

Definition ilab_of itl : Z :=
  match itl with
  | ilab _ n => n
  end.
