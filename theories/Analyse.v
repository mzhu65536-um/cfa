(** * Analyse : Analysis 0-CFA Framework  *)
(** In this chapter, we will present a more computable and syntax-directed
    analysis. The recipe for verifying, forming and solving the 0-CFA analysis 
    a la finite sets. 

    - Analyse:     Definition of the Analysis
    - Constraints: Converting a program into a finite set of analysis
    - Graph:       Graph formulation for efficient lfp solution
*) 

From CFA Require Export Ancilla.
From CFA Require Export Ordered.


(** ** Abstract Domains *)
Local Open Scope Z_scope.
Fixpoint lab_to_fon__aux (l : label) (tl : fon_l) : option fon_ :=
  match tl with
  | lab tl' l' =>
    if l =? l' then Some tl' else
      match tl' with
      | fon__app tl1 tl2 =>
        match (lab_to_fon__aux l tl1) with
        | Some tl' => Some tl'
        | None => (lab_to_fon__aux l tl2)
        end
      | fon__let x tl1 tl2 =>
        match (lab_to_fon__aux l tl1) with
        | Some tl' => Some tl'
        | None => (lab_to_fon__aux l tl2)
        end
      | fon__fun x tl1 => (lab_to_fon__aux l tl1)
      | fon__fix f x tl1 => (lab_to_fon__aux l tl1)
      | fon__cst c => None
      | fon__id x => None
      | fon__if tl1 tl2 tl3 =>
        match (lab_to_fon__aux l tl1) with
        | Some tl' => Some tl'
        | None => match (lab_to_fon__aux l tl2) with
                  | Some tl' => Some tl'
                  | None => (lab_to_fon__aux l tl3)
                  end
        end
      | fon__op op tl1 tl2 =>
        match (lab_to_fon__aux l tl1) with
        | Some tl' => Some tl'
        | None => (lab_to_fon__aux l tl2)
        end
      end
  end.

Definition lab_to_fon_ (l : label) (tl : fon_l) : fon_ :=
  match (lab_to_fon__aux l tl) with
  | Some t => t
  | None => fon__id x
  end.

Import SetFonl.
(** ** Fixpoint Approach  *)
(** ̂(C, ̂ρ) ⊨ λl as Fixpoint function *)
Local Open Scope bool_scope.
(* Follow the right principle, recurse on the structure of tl *)
Fixpoint analyse_s (ch : cache_hat) (eh : env_hat) (tl : fon_l)
         {struct tl} : bool :=
  let loop := analyse_s in
  match tl with
    lab t l => 
    match t with
    | fon__cst c => true
    | fon__id x =>
      (match (mfind x eh, mfind l ch) with
       | (Some vh1, Some vh2) => ssubset vh1 vh2
       | _ => false
       end)
    | fon__fun x tl' =>
      (match mfind l ch with
       | Some vh => (ssubset (sadd tl smt) vh)
       | _ => false
       end) && (loop ch eh tl')
    | fon__fix f x tl' =>
      (match mfind l ch with
       | Some vh => (ssubset (sadd tl smt) vh)
       | _ => false
       end) && (loop ch eh tl') &&
      (match mfind f eh with
       | Some vh => (ssubset (sadd tl smt) vh)
       | _ => false
       end)
    | fon__app ((lab t1 l1) as tl1) ((lab t2 l2) as tl2) =>
      (loop ch eh tl1) && (loop ch eh tl2) &&
      match mfind l1 ch, mfind l2 ch, mfind l ch with
      | Some vhf, Some vht, Some vhl =>
        for_all
          (fun tlf' =>
             match tlf' with
             | lab tf' lf' =>
               match tf' with
               | fon__fun x (lab _ l0)
               | fon__fix _ x (lab _ l0) =>
                 match mfind x eh, mfind l0 ch with
                 | Some vhx, Some vh0 =>
                   (andb (subset vht vhx) (subset vh0 vhl))
                 | _, _ => false
                 end
               | _ => true
               end
             end
          ) vhf
      | _, _, _ => false
      end
    | fon__if tlp tlt tlf =>
      match tlp, tlt, tlf with
      | lab _ lp', lab _ lt', lab _ lf' =>
        (loop ch eh tlp) && (loop ch eh tlt) && (loop ch eh tlf) &&
        match mfind lt' ch, mfind lf' ch, mfind l ch with
        | Some vht, Some vhf, Some vhl => (subset vht vhl) && (subset vhf vhl)
        | _, _, _ => false
        end
      end
    | fon__let x tl1 tl2 =>
      match tl1, tl2 with
      | lab _ l1', lab _ l2' =>
        (loop ch eh tl1) && (loop ch eh tl2) &&
        match mfind x eh, mfind l1' ch, mfind l2' ch, mfind l ch
        with
        | Some vhx, Some vh1, Some vh2, Some vhl =>
          (subset vh1 vhx) && (subset vh2 vhl)
        | _, _, _, _ => false
        end
      end
    | fon__op _ tl1 tl2 =>
      match tl1, tl2 with
      | lab _ l1', lab _ l2' =>
        (loop ch eh tl1) && (loop ch eh tl2)
      end
    end
  end.
Local Close Scope bool_scope.

(** A constant expression is acceptable under any abstract cache and
    abstract environment. *)
Theorem cst_acceptable :
  forall (ch : cache_hat) (eh : env_hat) (c : cst),
    analyse_s ch eh (label_fon_p (fon_p_cst c)) = true.
Proof. reflexivity. Qed.

(** ** Auxillary *)
Definition fon_l_to_set (e : fon_l) : val_hat :=
  sadd e smt.

Definition fon_l_to_simple_cache (lst : list (label * fon_l)) : cache_hat :=
  List.fold_left 
    (fun ys x => match x with (l, e) => madd l (fon_l_to_set e) ys end)
    lst mmt.


(** **** PoPA : Example 3.15 (example correctness of analysis_s)  *)
Import ListNotations.
Local Open Scope string_scope.
(* Case: Tight Approximation *)
Example example_ch1__tight : cache_hat :=
  madd
    3 smt 
    (fon_l_to_simple_cache
       [(5, (lab (fon__fun y (lab (fon__id y) 3)) 4));
       (4, (lab (fon__fun y (lab (fon__id y) 3)) 4));
       (2, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
       (1, (lab (fon__fun y (lab (fon__id y) 3)) 4))]).

Example example_eh1__tight : env_hat :=
  madd "y" smt
       (madd "x" (fon_l_to_set (lab (fon__fun y (lab (fon__id y) 3)) 4))
             mmt).


Example analyse_s_correct_1__tight :
  analyse_s example_ch1__tight example_eh1__tight (label_fon_p example_exp1) = true.
Proof. reflexivity. Qed.

(* Case: Over Approximation *)
Example example_ch1__over1 : cache_hat :=
  (fon_l_to_simple_cache
     [ (5, (lab (fon__fun y (lab (fon__id y) 3)) 4)) ;
       (4, (lab (fon__fun y (lab (fon__id y) 3)) 4)) ;
     (3, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
     (2, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
     (1, (lab (fon__fun y (lab (fon__id y) 3)) 4))
  ]).

Example example_eh1__over1 : env_hat :=
  madd y (fon_l_to_set (lab (fon__fun x (lab (fon__id x) 1)) 2))
       (madd x (fon_l_to_set (lab (fon__fun y (lab (fon__id y) 3)) 4))
             mmt).

Example analyse_s_correct1__over1 :
  analyse_s
    example_ch1__over1 example_eh1__over1 (label_fon_p example_exp1) = true.
Proof. reflexivity. Qed.

(* Case: Under Approximation *)
Example example_ch1__under : cache_hat :=
  (fon_l_to_simple_cache
     [ (5, (lab (fon__fun y (lab (fon__id y) 3)) 4)) ;
       (4, (lab (fon__fun y (lab (fon__id y) 3)) 4)) ;
     (3, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
     (2, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
     (1, (lab (fon__fun y (lab (fon__id y) 3)) 4))
  ]).

Example example_eh1__under : env_hat := mmt.

Example analyse_s_incorrect1__under :
  analyse_s
    example_ch1__under example_eh1__under (label_fon_p example_exp1) = false.
Proof. reflexivity. Qed.


(* Case: Incorrect Approximation *)
Example example_ch1__incorrect : cache_hat :=
  madd
    3 smt 
    (fon_l_to_simple_cache
       [(5, (lab (fon__fun y (lab (fon__id y) 3)) 4));
       (4, (lab (fon__fun x (lab (fon__id x) 1)) 2)) ;
       (2, (lab (fon__fun y (lab (fon__id y) 3)) 4));
       (1, (lab (fon__fun y (lab (fon__id y) 3)) 4))]).

Example example_eh1__incorrect : env_hat :=
  madd "y" smt
       (madd "x" (fon_l_to_set (lab (fon__fun y (lab (fon__id y) 3)) 4))
             mmt).


Example analyse_s_incorrect_1__incorrect :
  analyse_s
    example_ch1__incorrect example_eh1__incorrect (label_fon_p example_exp1)
  = false.
Proof. reflexivity. Qed.


(** ** Preservation of Solutions  *)
(** The previous examples show that if an analysis is correct for one, then
    the over-approaximation of the analysis will also holds, now, let's 
    mechanize this specification. 

    In the book, this proof is acomplished by coinduction on lattice, let's try 
    another approach.
 *)



Definition cache_hat_le' (C1 C2 : cache_hat) : Prop :=
  forall (l : label) (vh1 : val_hat),
    mfind l C1 = Some vh1 -> 
    exists vh2, mfind l C2 = Some vh2 /\ ssubset vh1 vh2 = true
.


Definition env_hat_le' (R1 R2 : env_hat) : Prop :=
  forall (r : string) (vh1 : val_hat),
    mfind r R1 = Some vh1 -> 
    exists vh2, mfind r R2 = Some vh2 /\ ssubset vh1 vh2 = true
.

Definition cheh_le (C1 C2 : cache_hat) (R1 R2 : env_hat) : Prop := 
  (cache_hat_le' C1 C2) /\ (env_hat_le' R1 R2)
.

Theorem analyse_s_over :
  forall (tl : fon_l) (C1 C2 : cache_hat) (R1 R2 : env_hat) ,
    cheh_le C1 C2 R1 R2 ->
    analyse_s C1 R1 tl = true ->
    analyse_s C2 R2 tl = true.
Proof.
Admitted.


