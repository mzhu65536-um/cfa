(** * Contraints : Constraints-based CFA-0 Analysis *)
From CFA Require Export Analyse.
From CFA Require Export Ordered.
From CFA Require Export Ancilla.
(* From CFA Require Export Decidable. *)

(** In this chapter, in order to proceed to the graph approach to solve for 
    0-CFA, let's take a detour to convert the analysis to contraints first.
 *)

(** [constraint] is either subset or implication relation / set*)

(** Set implimentation  *)

(** 
<<
    {t} ::= val_hat  
      C ::= cache_hat (label -> val_hat)
      r ::= env_hat (String -> val_hat)
>>
 *)

Import Bundle.

Definition consub1 (lhs rhs : bundle) := ssingle (con_sub lhs rhs).
Definition conimp (lhs1 rhs1 lhs2 rhs2 : bundle) :=
  ssingle (con_imp (con_sub lhs1 rhs1) (con_sub lhs2 rhs2)).

(** Interface to make env, cache, or term element in constraints *)
Definition env_constr (x : var) := b_r x.
Definition cache_constr (l : label) := b_c l.
Definition t_constr (tl : fon_l) := b_t tl.

Fixpoint subterms (tl : fon_l) : val_hat :=
  match tl with
    lab t l =>
    match t with
    | fon__app tl1 tl2 =>
      sunion (subterms tl1) (subterms tl2)
    | fon__if tl1 tl2 tl3 =>
      sunion (sunion (subterms tl1) (subterms tl2)) (subterms tl3)
    | fon__let _ tl1 tl2 =>
      sunion (subterms tl1) (subterms tl2)
    | fon__op _ tl1 tl2 =>
      sunion (subterms tl1) (subterms tl2)
    | _ => sadd tl smt
    end
  end.

(** To encode constraints as P(constraint), we need a set *)

Fixpoint gen_constraints (tl : fon_l) : constr :=
  match tl with
    lab t l =>
    match t with
    | fon__cst c => smt
    | fon__id x => consub1 (env_constr x) (cache_constr l)
    | fon__fun x tl' =>
      let constrs0 := gen_constraints tl' in
      let constrs1 := consub1 (t_constr tl) (cache_constr l) in
      sunion constrs0 constrs1
    | fon__fix f x tl' =>
      let constrs0 := consub1 (t_constr tl) (cache_constr l) in
      let constrs1 := gen_constraints tl' in
      let constrs2 := consub1 (t_constr tl) (env_constr f) in
      sunion (sunion constrs0 constrs1) constrs2
    | fon__app ((lab t1 l1) as tl1) ((lab t2 l2) as tl2) =>
      let constrs0 := gen_constraints tl1 in
      let constrs1 := gen_constraints tl2 in
      let app_aux (tl' : fon_l) (acc : constr) : constr :=
          match tl' with
            lab t' l' =>
            match t' with
            | fon__fun x (lab _ l0)
            | fon__fix _ x (lab _ l0) =>
              let constrs0 := conimp (t_constr tl') (cache_constr l1)
                                     (cache_constr l2) (env_constr x) in
              let constrs1 := conimp (t_constr tl') (cache_constr l1)
                                     (cache_constr l0) (cache_constr l) in
              sunion (sunion constrs0 constrs1) acc
            | _ => acc
            end
          end in
      sfold app_aux (subterms tl) (sunion (sunion constrs0 constrs1) smt)
    | fon__if ((lab t1 l1) as tl1) ((lab t2 l2) as tl2) ((lab t3 l3) as tl3) =>
      let constrs0 := gen_constraints tl1 in
      let constrs1 := gen_constraints tl2 in
      let constrs2 := gen_constraints tl3 in
      let constrs3 := consub1 (cache_constr l1) (cache_constr l) in
      let constrs4 := consub1 (cache_constr l2) (cache_constr l) in
      sunion (sunion (sunion (sunion constrs0 constrs1) constrs2) constrs3) constrs4
    | fon__let x ((lab t1 l1) as tl1) ((lab t2 l2) as tl2) =>
      let constrs0 := gen_constraints tl1 in
      let constrs1 := gen_constraints tl2 in
      let constrs2 := consub1 (cache_constr l1) (env_constr x) in
      let constrs3 := consub1 (cache_constr l2) (cache_constr l) in
      sunion (sunion (sunion constrs0 constrs1) constrs2) constrs3
    | fon__op _ ((lab t1 l1) as tl1) ((lab t2 l2) as tl2) =>
      let constrs0 := gen_constraints tl1 in
      let constrs1 := gen_constraints tl2 in
      sunion constrs0 constrs1
    end
  end.

Import ListNotations.
Local Open Scope Z_scope.
Definition id_x : fon_l := lab (fon__fun x (lab (fon__id x) 1)) 2.
Definition id_y : fon_l := lab (fon__fun y (lab (fon__id y) 3)) 4.
Definition add_constraints (lst : list constraint) : constr :=
  List.fold_left (fun ys x => sadd x ys) lst smt.
Example cstr_ex1 := (gen_constraints (label_fon_p example_exp1)).
Example cstr_ex1_expect : constr :=
  add_constraints
    [ con_sub (t_constr id_x) (cache_constr 2) ;
    con_sub (env_constr x) (cache_constr 1) ;
    con_sub (t_constr id_y) (cache_constr 4) ;
    con_sub (env_constr y) (cache_constr 3) ;
    con_imp (con_sub (t_constr id_x) (cache_constr 2))
            (con_sub (cache_constr 4) (env_constr x)) ;
    con_imp (con_sub (t_constr id_x) (cache_constr 2))
            (con_sub (cache_constr 1) (cache_constr 5)) ;
    con_imp (con_sub (t_constr id_y) (cache_constr 2))
            (con_sub (cache_constr 4) (env_constr y)) ;
    con_imp (con_sub (t_constr id_y) (cache_constr 2))
            (con_sub (cache_constr 3) (cache_constr 5))
    ].
Example cstr_ex1_correct : sequal cstr_ex1 cstr_ex1_expect = true.
Proof. reflexivity. Qed.


(** * Graph : Graph Formulation for CFA-0 Analysis *)
(** 
<<
    queue ::= gqueue
    data  ::= gdata (bundle -> val_hat)
    edge  ::= gedge (bundle -> constraint)
>>
 *)
Definition graph : Type := gqueue * gdata * gedge.

(** ** Graph Initialization *)
(** initialize_graph_aux is a recursive function for gathering all
    nodes in the expression into the graph representation. *)
Fixpoint initialize_graph_aux (tl : fon_l) (data : gdata) (edge : gedge)
  : gdata * gedge :=
  match tl with
    lab t l =>
    let data : gdata := (madd (b_c l) smt data) in
    let edge : gedge := (madd (b_c l) smt edge) in
    match t with
    | fon__cst _ => (data, edge)
    | fon__id x => ((madd (b_r x) smt data), (madd (b_r x) smt edge))
    | fon__fun x tl' => initialize_graph_aux
                        tl' (madd (b_r x) smt data) (madd (b_r x) smt edge)
    | fon__fix f x tl' => initialize_graph_aux
                          tl' (madd (b_r x) smt (madd (b_r f) smt data))
                          (madd (b_r x) smt (madd (b_r f) smt edge))
    | fon__app tl1 tl2 =>
      let (data, edge) := initialize_graph_aux tl1 data edge in
      initialize_graph_aux tl2 data edge
    | fon__if tl1 tl2 tl3 =>
      let (data, edge) := initialize_graph_aux tl1 data edge in
      let (data, edge) := initialize_graph_aux tl2 data edge in
      initialize_graph_aux tl3 data edge
    | fon__let x tl1 tl2 =>
      let (data, edge) := ((madd (b_r x) smt data), (madd (b_r x) smt edge)) in
      let (data, edge) := initialize_graph_aux tl1 data edge in
      initialize_graph_aux tl2 data edge
    | fon__op _ tl1 tl2 =>
      let (data, edge) := initialize_graph_aux tl1 data edge in
      initialize_graph_aux tl2 data edge
    end
  end.

Definition initialize_graph (tl : fon_l): graph :=
  let queue : gqueue := smt in
  let (data, edge) := initialize_graph_aux tl mmt mmt in
  (queue, data, edge).

Example init_graph_exp1 : graph :=
  let queue : gqueue := smt in
  let data : gdata := mmt in
  let edge : gedge := mmt in
  (queue, List.fold_left
            (fun ys v => madd v smt ys)
            (List.map (fun x => b_r x) [x;y])
            (List.fold_left (fun ys x => madd x smt ys)
                            (List.map (fun l => b_c l) [1;2;3;4;5]) data),
   List.fold_left
     (fun ys x => madd x smt ys)
     (List.map (fun x => b_r x) [x;y])
     (List.fold_left (fun ys x => madd x smt ys)
                     (List.map (fun l => b_c l) [1;2;3;4;5]) edge)).

Definition graph_equal (g1 g2 : graph) : bool :=
  match (g1, g2) with
    ((q1, d1, e1), (q2, d2, e2)) =>
    andb (andb (sequal q1 q2) (mequal d1 d2)) (mequal e1 e2)
  end.
  
Example init_graph_correct :
  graph_equal (initialize_graph (label_fon_p example_exp1))
              init_graph_exp1 = true.
Proof. reflexivity. Qed.

(** ** Graph Construction  *)
(* ** Auxillary for graph construction *)

(** add_node incorporates fon_l into dataset and adds node to queue if
    necessary. *)         
Definition add_node (queue : gqueue) (data : gdata) (node t : bundle)
  : gqueue * gdata :=
  match t with
  | b_t t =>
    match mfind node data with
    | Some vhs =>
      if SetBundle.mem node queue
      then (queue, (madd node (sadd t vhs) data))
      else ((sadd node queue), (madd node (sadd t vhs) data))
    | None => (queue, data)
    end
  | _ => (queue, data)
  end.

Definition add_edge (edge : gedge) (node : bundle) (cc : constraint)
  : gedge :=
  match mfind node edge with
  | Some ccs =>
    madd node (sadd cc ccs) edge
  | None => madd node (ssingle cc) edge
  end.

Fixpoint gen_graph_aux (cstr : list constraint) (queue : gqueue)
         (data : gdata) (edge : gedge) : graph :=
  match cstr with
  | c :: cstr =>
    match c with
    | con_sub (b_t t) rhs =>
      let (queue, data) := add_node queue data rhs (b_t t) in
      gen_graph_aux cstr queue data edge
    | con_sub lhs rhs =>
      gen_graph_aux cstr queue data (add_edge edge lhs c)
    | con_imp (con_sub _ rhs1) (con_sub lhs2 rhs2) =>
      let edge := add_edge edge lhs2 c in
      let edge := add_edge edge rhs1 c in
      gen_graph_aux cstr queue data edge
    | _ => (queue, data, edge)
    end
  | _ => (queue, data, edge)
  end.

(** gen_graph initializes a graph for a given term by building initial
    queue, dataset, and edge set *)
Definition gen_graph (tl : fon_l) : graph :=
  let cstr : list constraint := selements (gen_constraints tl) in
  let graph := initialize_graph tl in
  match graph with
    (queue, data, edge) =>
    gen_graph_aux cstr queue data edge
  end.

(** We need to test correctness of gen_graph by encoding the expected
    graph of (λx. x) (λy. y) *)
Example data_exp1 : gdata :=
  let mt_vhs : val_hat := smt in
  List.fold_left
    (fun (acc : gdata) (prod : bundle * val_hat) =>
       match prod with
         (node, vhs) => madd node vhs acc
       end)
    [ ((b_c 1), mt_vhs) ;
    ((b_c 2), (ssingle id_x));
    ((b_c 3), mt_vhs) ;
    ((b_c 4), (ssingle id_y));
    ((b_c 5), mt_vhs) ;
    ((b_r x), mt_vhs) ;
    ((b_r y), mt_vhs) ]
    mmt.
Example edge_exp1 : gedge :=
  let id_xc :=
      con_imp (con_sub (b_t id_x) (b_c 2)) (con_sub (b_c 1) (b_c 5)) in
  let id_xr :=
      con_imp (con_sub (b_t id_x) (b_c 2)) (con_sub (b_c 4) (b_r x)) in
  let id_yc :=
      con_imp (con_sub (b_t id_y) (b_c 2)) (con_sub (b_c 3) (b_c 5)) in
  let id_yr :=
      con_imp (con_sub (b_t id_y) (b_c 2)) (con_sub (b_c 4) (b_r y)) in
  let f (acc : gedge) (prod : bundle * list constraint) : gedge :=
      let mt_cstr : constr := smt in
      match prod with
        (node, ccs) => madd node (List.fold_left
                                    (fun ys x => sadd x ys)
                                    ccs mt_cstr) acc end in
  List.fold_left f [ ((b_c 1), [id_xc]) ;
                   ((b_c 2), [id_yc; id_yr; id_xc; id_xr]) ;
                   ((b_c 3), [id_yc]) ;
                   ((b_c 4), [id_yr; id_xr]) ;
                   ((b_c 5), []) ;
                   ((b_r x), [(con_sub (b_r x) (b_c 1))]) ;
                   ((b_r y), [(con_sub (b_r y) (b_c 3))])]
                 mmt.
Example gen_graph_exp1 : graph :=
  let queue : gqueue := (sadd (b_c 2) (sadd (b_c 4) smt)) in
  (queue, data_exp1, edge_exp1).

Example test :=
  match gen_graph_exp1, (gen_graph (label_fon_p example_exp2)) with
    (q1, d1, e1), (q2, d2, e2) =>
    (List.map (fun x =>  ((fst x), SetConstr.elements (snd x))) (MapNodes.elements e1),
     List.map (fun x =>  ((fst x), SetConstr.elements (snd x))) (MapNodes.elements e2))
  end.
Compute test.

Example gen_graph_correct :
  graph_equal gen_graph_exp1
              (gen_graph (label_fon_p example_exp1)) = true.
Proof. reflexivity. Qed.

(** ** Traversing the Graph *)
(** The next step is to traverse the graph and obtain the resulting
    dataset for abstract cache and abstract environment *)

(* ** Auxillary : list representation for queue *)
Definition qmem (elem : bundle) (lst : list bundle) : bool :=
  List.existsb (fun x => if Bundle_as_DT.eq_dec x elem
                         then true else false) lst.

Definition qadd (elem : bundle) (lst : list bundle) : list bundle :=
  if qmem elem lst then lst else elem :: lst.

(** Auxillary function defined earlier needs to accomodate for the
    list representation. *)
Definition add_node' (queue : list bundle) (data : gdata) (node t : bundle)
  : list bundle * gdata :=
  match t with
  | b_t t =>
    match mfind node data with
    | Some vhs =>
      if qmem node queue
      then (queue, (madd node (sadd t vhs) data))
      else (node :: queue, (madd node (sadd t vhs) data))
    | None => (queue, data)
    end
  | _ => (queue, data)
  end.

(** add_node_multi is a more general version of add_node which could
    incorporate val_hat to a node's dataset *)
Definition add_node_multi (queue : list bundle) (data : gdata) (node : bundle)
           (d : val_hat) : (list bundle) * gdata :=
  List.fold_left
    (fun (ys : list bundle * gdata) (x : bundle) =>
       let (queue', data') := ys in
       add_node' queue' data' node x)
    (List.fold_left
       (fun (ys : list bundle) (x : fon_l) => qadd (b_t x) ys)
       (selements d) [])
    (queue, data).

Fixpoint trav_node (queue : list bundle) (data : gdata)
         (edge_g : gedge) (ccs : list constraint) :
  list bundle * gdata :=
  match ccs with
  | cc :: ccs =>
    match cc with
    | con_sub lhs rhs =>
      match mfind lhs data with
      | Some d =>
        let (queue, data) := add_node_multi queue data rhs d in
        trav_node queue data edge_g ccs
      | None => (queue, data)
      end
    | con_imp (con_sub (b_t t) rhs1) (con_sub lhs2 rhs2) =>
      match (mfind rhs1 data) with
      | Some d1 =>
        if SetFonl.mem t d1 then
          match mfind lhs2 data with
          | Some d2 =>
            let (queue, data) := add_node_multi queue data rhs2 d2 in
            trav_node queue data edge_g ccs
          | None => (queue, data)
          end
        else trav_node queue data edge_g ccs
      | None => (queue, data)
      end
    | _ => trav_node queue data edge_g ccs
    end
  | [] => (queue, data)
  end.

Fixpoint trav_graph_aux (queue : list bundle) (data : gdata) (edge :gedge)
         (fuel : nat) : list bundle * gdata :=
  match fuel with
  | O => (queue, data)
  | S fuel =>
    match queue with
    | node :: queue =>
      match mfind node edge with
      | Some ccs =>
        let (queue, data) := trav_node queue data edge (selements ccs) in
        trav_graph_aux queue data edge fuel
      | None => (queue, data)
      end
    | [] => (queue, data)
    end
  end.

(** trav_graph : traverses the graph and returns resulting dataset.  
    A fuel is used to ensure termination due to the potentially
    unbounded behavior for queue manipulation. *)
Definition trav_graph (tl : fon_l) : gdata :=
  let fuel := 1000%nat in
  let cstr : list constraint := selements (gen_constraints tl) in
  let graph := gen_graph tl in
  match graph with
    (queue, data, edge) =>
    snd (trav_graph_aux (selements queue) data edge fuel)
  end.

(** To roughly test correctness of the constraint-based analysis,
    the term (λx. x) (λy. y) is again used. *)
Example data_exp' : gdata :=
  List.fold_left
    (fun (ys : gdata) (x : bundle * list fon_l) =>
       let (node, vhs) := x in
       (madd node (List.fold_left
                     (fun (ys : val_hat) (x : fon_l) => sadd x ys)
                     vhs smt) ys))
    [ ((b_c 1), [id_y]) ;
    ((b_c 2), [id_x]) ;
    ((b_c 3), []) ;
    ((b_c 4), [id_y]) ;
    ((b_c 5), [id_y]) ;
    ((b_r x), [id_y]) ;
    ((b_r y), []) ]
    mmt.
Example trav_graph_correct :
  mequal (trav_graph (label_fon_p example_exp1)) data_exp' = true.
Proof. reflexivity. Qed.


(** ** Constraint-Based 0-CFA Analysis  *)
(** Here we define 0-CFA analysis which takes a labeled lambda
    expression and returns corresponding abstract cache and abstract
    environment. *)
Definition O_CFA (tl : fon_l) : cache_hat * env_hat :=
  let gdata := trav_graph tl in
  List.fold_left
    (fun (ys : cache_hat * env_hat) (x : bundle * val_hat) =>
       let (ch, eh) := ys in
       match x with
       | (b_c l, tl) => ((madd l tl ch), eh)
       | (b_r x, tl) => (ch, (madd x tl eh))
       | _ => (ch, eh)
       end)
    (MapNodes.elements gdata)
    (mmt, mmt).

Example O_CFA_cst :=
  let tl := (label_fon_p (fon_p_cst (c_Z 1))) in
  match O_CFA tl with
  | (C, R) =>
    ((MapLabel_.elements C), (MapString_.elements R))
  end.
Compute O_CFA_cst.

Example O_CFA_exp :=
  let tl := (label_fon_p example_exp1) in
  match O_CFA tl with
  | (C, R) => analyse_s C R tl
  end.

Example O_CFA_exp_correct : O_CFA_exp = true.
Proof. reflexivity. Qed.

(** **** exercise : 4 star, prove they_are_good formally *)
Theorem they_are_good :
  forall (tl : fon_l),
    match O_CFA tl  with
    | (C, R) => analyse_s C R tl = true
    end.
Proof.
Admitted.


