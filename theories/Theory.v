(** * Theory : Theoretical Basis of 0-CFA Analysis  *)
(** In this chapter, we study properties of 0-CFA analysis including 
    
    - Well-foundness
    - Facts on CFA
    - Existence of Least Solution
 *)
From CFA Require Export Coqlib.
From CFA Require Export Lang.
From CFA Require Export Ancilla.

(** ** Accept an analysis *)

(** ⊨ : CacheH -> EnvH -> Exp -> Prop *)

(* fix me:  notation  *)
Reserved Notation "'<{' C ',' R '}>' '⊨' tl"
         (at level 195, left associativity).

Module Analysis0.
  Import SetFonl.
  (** Inductive definition of acceptability of analyse *)
  CoInductive analyse (C : cache_hat)  (R : env_hat) : fon_l -> Prop :=
  | a__cons (l : label) (c : cst) :
      <{C, R}> ⊨ (lab (fon__cst c) l)
  | a__var (l : label) (s : var) (vh1 vh2 : val_hat):
      mMapsTo s vh1 R ->
      mMapsTo l vh2 C ->
      Subset vh1  vh2 ->
      <{C, R}> ⊨ (lab (fon__id s) l)
  | a__fun (l : label) (x : var) (tl : fon_l) (vh : val_hat) :
      mMapsTo l vh C ->
      Subset (singleton (lab (fon__fun x tl) l)) vh -> 
      <{C, R}> ⊨ (lab (fon__fun x tl) l)
  | a__fix (l : label) (x f : var) (tl : fon_l) (vh : val_hat) :
      mMapsTo l vh C ->
      Subset (singleton (lab (fon__fix f x tl) l)) vh -> 
      <{C, R}> ⊨ (lab (fon__fix f x tl) l)
  | a__app (l l1 l2  : label) (t1 t2 : fon_) (vh vh1 vh2 : val_hat) :
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      mMapsTo l vh C ->         
      (<{C, R}> ⊨ (lab t1 l1)) ->
      (<{C, R}> ⊨ (lab t2 l2)) ->
      (* Caveat: In this case, we cannot assert that [t'] is structually smaller 
       than [t1] or [t2]. Thus, this relation is coinductively defined 
       (i.e. we are define it on infinity).
       *)
      (forall (x : var) (t' : fon_) (l' lf : label) (vh' vhx : val_hat),
          Subset (singleton (lab (fon__fun x (lab t' l')) lf)) vh1 ->
          mMapsTo x vhx R ->
          ((<{C, R}> ⊨ (lab t' l')) /\
           (Subset vh2 vhx) /\
           (Subset vh' vh))) ->
      (forall (f x : var) (t' : fon_) (l' lf : label) (vh' vhf vhx : val_hat),
          Subset (singleton (lab (fon__fix f x (lab t' l')) lf)) vh1 ->
          mMapsTo x vhx R ->
          mMapsTo f vhf R ->        
          Subset (singleton (lab (fon__fix f x (lab t' l')) lf)) vhf /\
          ((<{C, R}> ⊨ (lab t' l')) /\
           (Subset vh2 vhx) /\
           (Subset vh' vh)))  ->
      <{C, R}> ⊨ (lab (fon__app (lab t1 l1) (lab t2 l2)) l)
  | a__if (l l0 l1 l2 : label) (t0 t1 t2 : fon_) (vh vh1 vh2 : val_hat):
      mMapsTo l vh C ->
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      (<{C, R}> ⊨ (lab t0 l0)) ->  
      (<{C, R}> ⊨ (lab t1 l1)) ->
      (<{C, R}> ⊨ (lab t2 l2)) ->
      Subset vh1 vh ->
      Subset vh2 vh ->
      <{C, R}> ⊨ (lab (fon__if (lab t0 l0) (lab t1 l1) (lab t2 l2)) l)
  | a__let (x : var) (l l1 l2 : label) (t1 t2 : fon_) (vh vh1 vh2 vhx : val_hat):
      mMapsTo l vh C ->
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      mMapsTo x vhx R ->
      Subset vh2 vh ->
      Subset vh1 vhx ->  
      (<{C, R}> ⊨ (lab t1 l1)) ->
      (<{C, R}> ⊨ (lab t2 l2)) ->
      <{C, R}> ⊨ (lab (fon__let x (lab t1 l1) (lab t2 l2)) l)
  | a__op (t1 t2 : fon_) (l l1 l2 : label) (o : op) :
      (<{C, R}> ⊨ (lab t1 l1)) ->
      (<{C, R}> ⊨ (lab t2 l2)) ->
      <{C, R}> ⊨ (lab (fon__op o (lab t1 l1) (lab t2 l2)) l)
  where  "'<{' C ',' R '}>' '⊨' tl" := (analyse C R tl)
  .

  (** ** Lattice (Skipped) *)
  Theorem analyse_lfp : True. Admitted.
End Analysis0.


(** ** Structural Semantics of Intermediate FON Language *)
Reserved Notation "r ⊢ e1 '--->' e2"
         (at level 190, left associativity).

Inductive value : ifon_l -> Prop :=
| v_cst (c : cst) (l : label) :
    value (ilab (ifon__cst c) l)
| v_cls (t : fon_) (r : env) (l : label):
    value (ilab (ifon__cls t r) l)
.

Definition inj_ival (l : label) (iv : ival) : ifon_l :=
  ilab 
    (match iv with 
     | iv_cls t r => ifon__cls t r
     | iv_cst c => ifon__cst c
     end)
    l
.

Definition proj_value (itl : ifon_l) : ival :=
  match itl with
  | ilab it _ =>
    match it with
    | ifon__cst c => iv_cst c
    | ifon__cls t r => iv_cls t r
    | _ => iv_cst (c_bool false)  (* impossible *)
    end
  end
.
  
(** Metafunction for [op] evaluation  *)
Definition eval_op (op : op) (l : label) (itl1 itl2 : ifon_l) : ifon_l :=
  match itl1, itl2 with
  | ilab (ifon__cst c1) _, ilab (ifon__cst c2) _ =>
    match c1, c2 with
    | c_Z z1, c_Z z2 =>
      match op with
      | op__equal => ilab (ifon__cst
                           (c_bool (if Z.eqb z1 z2 then true else false))) l
      | _ => ilab (ifon__cst
                     (c_Z (match op with
                           | op__plus => z1 + z2
                           | op__minus => z1 - z2
                           | op__mult => z1 * z2
                           | _ => 0 (* impossible *)
                           end))) l
      end
    | _, _ => (ilab (ifon__op op itl1 itl2) l)
    end
  | _, _ => (ilab (ifon__op op itl1 itl2) l)
  end
.

(** ** Smallstep Semantics for Intermediaire FON *)
(**
   However, I believe there are some problems with the ordered type where I  
   simply compare their label. It will work (hopefully) in the constraint-based 
   analysis. But, the evalution by [step] could mess up the label, which in turn
   leads to incorrect result.


   TODO: Redefine [eq] in [IFon_as_OT] as an Inductive on the shape of the  
         expression.
 *)

Inductive step (r : env) : ifon_l -> ifon_l -> Prop :=
| s__var (l : label) (x : var) (v : ival) :
    get_env x r = Some v ->
    r ⊢ (ilab (ifon__id x) l) ---> inj_ival l v
| s__fun (l : label) (x : var) (tl : fon_l) :
    r ⊢
      (ilab (ifon__fun x tl) l) --->
      (ilab (ifon__cls (fon__fun x tl) r) l)
| s__fix (l : label) (f x : var) (tl : fon_l) :
    r ⊢
      (ilab (ifon__fix f x tl) l) --->
      (ilab (ifon__cls (fon__fix f x tl) r) l)
| s__app1 (l : label) (itl1 itl1' itl2 : ifon_l) :
    (r ⊢ itl1 ---> itl1') ->
    r ⊢ (ilab (ifon__app itl1 itl2) l) ---> (ilab (ifon__app itl1' itl2) l)
| s__app2 (l : label) (itl1 itl2 itl2' : ifon_l) :
    value itl1 -> 
    (r ⊢ itl2 ---> itl2') ->
    r ⊢ (ilab (ifon__app itl1 itl2) l) ---> (ilab (ifon__app itl1 itl2') l)
| s__appfun (l1 l : label) (x : var) (tl : fon_l) (itl : ifon_l)
          (r1 : env):
    value itl -> 
    r ⊢
      (ilab (ifon__app (ilab (ifon__cls (fon__fun x tl) r1) l1) itl) l)
      --->
      (ilab (ifon__bnd (extend_env x (proj_value itl) r1) itl) l)
| s__appfix (l1 l : label) (f x : var) (tl : fon_l) (itl0 itl : ifon_l)
          (r1 : env):
    itl0 = (ilab (ifon__cls (fon__fix f x tl) r1) l1) ->
    value itl -> 
    r ⊢
      (ilab (ifon__app itl0 itl) l)
      --->
      (ilab (ifon__bnd
               (extend_env f (proj_value itl0)
                           (extend_env x (proj_value itl) r1))
               itl) l)
| s__bind1 (l : label) (itl1 itl2 : ifon_l) (r1 : env) :
    (r1 ⊢ itl1 ---> itl2) ->
    r ⊢ (ilab (ifon__bnd r1 itl1) l) ---> (ilab (ifon__bnd r1 itl2) l)
| s__bind2 (l l1 : label) (it1 : ifon_) (r1 : env) :
    value (ilab it1 l1) -> 
    r ⊢ (ilab (ifon__bnd r1 (ilab it1 l1)) l) ---> (ilab it1 l)
| s__if1 (l : label) (itl0 itl0' itl1 itl2 : ifon_l) :
    (r ⊢ itl0 ---> itl0') ->
    (r ⊢
       (ilab (ifon__if itl0 itl1 itl2) l)
       --->
       (ilab (ifon__if itl0' itl1 itl2) l))
| s__ift (l l1 : label) (itl1 itl2 : ifon_l) :
    r ⊢
      (ilab (ifon__if (ilab (ifon__cst (c_bool true)) l1) itl1 itl2) l)
      --->
      itl1
| s__iff (l l1 : label) (itl1 itl2 : ifon_l) :
    r ⊢
      (ilab (ifon__if (ilab (ifon__cst (c_bool false)) l1) itl1 itl2) l)
      --->
      itl2
| s__let1 (l : label) (x : string) (itl0 itl0' itl1 : ifon_l) :
    (r ⊢ itl0 ---> itl0') ->
    (r ⊢
       (ilab (ifon__let x itl0 itl1) l)
       --->
       (ilab (ifon__let x itl0' itl1) l))
| s__let2 (l : label) (x : string) (itl0 itl1 : ifon_l) :
    value itl0 ->
    (r ⊢
       (ilab (ifon__let x itl0 itl1) l)
       --->
       (ilab (ifon__bnd (extend_env x (proj_value itl0) r) itl1) l))
| s__op1 (l : label) (itl1 itl1' itl2 : ifon_l) (op : op): 
    (r ⊢ itl1 ---> itl1') ->
    (r ⊢
       (ilab (ifon__op op itl1 itl2) l)
       --->
       (ilab (ifon__op op itl1' itl2) l))
| s__op2 (l : label) (itl1 itl2 itl2' : ifon_l) (op : op): 
    value itl1 ->
    (r ⊢ itl2 ---> itl2') ->
    (r ⊢
       (ilab (ifon__op op itl1 itl2) l)
       --->
       (ilab (ifon__op op itl1 itl2') l))
| s__op3 (l : label) (itl1 itl2 : ifon_l) (op : op): 
    value itl1 ->
    value itl2 ->
    (r ⊢
       (ilab (ifon__op op itl1 itl2) l)
       --->
       (eval_op op l itl1 itl2))
where  "r ⊢ e1 '--->' e2" := (step r e1 e2) . 


Definition ctx_rel (Ctx Object : Type) := Ctx -> Object -> Object -> Prop.
Check ctx_rel.

Inductive compatible_closure {Ctx Obj : Type} (R : ctx_rel Ctx Obj) :
  ctx_rel Ctx Obj :=
| cc_refl (r : Ctx) (o : Obj) : compatible_closure R r o o
| cc_step (r  : Ctx) (o1 o2 o3 : Obj) :
    R r o1 o2 ->
    compatible_closure R r o2 o3 ->
    compatible_closure R r o1 o3
.


(** **** [PoPA] Example 3.7 *)
Example cc_exp1 :
  (compatible_closure step)
    empty_env
    (inj (label_fon_p example_exp1))
    (ilab (ifon__cls (fon__fun y (lab (fon__id y) 3)) empty_env) 5).
Admitted.

(** Analysis of (lλ) *)
Module AnalysisI.

  (** We are operating on the different language, so we need to redefine
      everything we have done in Ancilla.
   *)
  
  (** ̂ {Val} :: P(iλl)  *)
  Definition val_hat : Type := SetIFonl.t. 

  (** ̂ {Env} :: String -> ^{Val} *)
  Definition env_hat : Type := MapString_.t val_hat.

  (** ̂ {Cache} :: Label -> ^{Val} *)
  Definition cache_hat : Type := MapLabel_.t val_hat.

  Import SetIFonl.

  Instance ValHatSet : CSet ifon_l SetIFonl.t :=
    {
    ssingle := SetIFonl.singleton;
    selements := SetIFonl.elements;
    sadd := SetIFonl.add;
    sunion := SetIFonl.union;
    smt := SetIFonl.empty;
    ssubset := SetIFonl.subset;
    sfor_all := SetIFonl.for_all;
    sfold := SetIFonl.fold;
    seq := SetIFonl.eq;
    seq_trans := SetIFonl.eq_trans;
    sequal := SetIFonl.equal;
    schoose := SetIFonl.choose;
    sremove := SetIFonl.remove;
    seq_dec := SetIFonl.eq_dec
    }
  .


  Instance EnvHatMap : CMap var val_hat (MapString_.t val_hat) :=
    {
    mequal := MapString_.equal sequal;
    madd k v m := @MapString_.add val_hat k v m;
    mfind k m := @MapString_.find val_hat k m;
    mremove k m := @MapString_.remove val_hat k m;
    mmt := MapString_.empty val_hat;
    mMapsTo := @MapString_.MapsTo val_hat
    }
  .

  Instance CacheHatMap : CMap label val_hat (MapLabel_.t val_hat) :=
    {
    mequal := MapLabel_.equal sequal;
    madd k v m := @MapLabel_.add val_hat k v m;
    mfind k m := @MapLabel_.find val_hat k m;
    mmt := MapLabel_.empty val_hat;
    mMapsTo := @MapLabel_.MapsTo val_hat;
    mremove k m := @MapLabel_.remove val_hat k m;
    }
  .


  Definition subdomain (r : env) (R : env_hat) : Prop :=
    forall x v,
      get_env x r = Some v ->
      exists v', mMapsTo x v' R. 

  (** Correctness Relation *)
  Inductive correct : env -> env_hat -> Prop :=
  | c_r (r : env) (R : env_hat) :
    subdomain r R ->
    (* FIXME : this relation looks weird *)
    forall x tx rx, get_env x rx = Some (iv_cls tx rx) ->
      (forall v', mMapsTo x v' R -> correct rx R) ->
      correct r R
  .
                

  (** Inductive definition of acceptability of analyse *)
  (** FIXME : Should this be CoInd?  *)
  Inductive analyse (C : cache_hat)  (R : env_hat) : ifon_l -> Prop :=
  | a__cons (l : label) (c : cst) :
      <{C, R}> ⊨ (ilab (ifon__cst c) l)
  | a__var (l : label) (s : var) (vh1 vh2 : val_hat):
      mMapsTo s vh1 R ->
      mMapsTo l vh2 C ->
      Subset vh1  vh2 ->
      <{C, R}> ⊨ (ilab (ifon__id s) l)
  | a__fun (l : label) (x : var) (tl : fon_l) (vh : val_hat) :
      mMapsTo l vh C ->
      Subset (singleton (ilab (ifon__fun x tl) l)) vh -> 
      <{C, R}> ⊨ (ilab (ifon__fun x tl) l)
  | a__fix (l : label) (x f : var) (tl : fon_l) (vh : val_hat) :
      mMapsTo l vh C ->
      Subset (singleton (ilab (ifon__fix f x tl) l)) vh -> 
      <{C, R}> ⊨ (ilab (ifon__fix f x tl) l)
  | a__app (l l1 l2  : label) (t1 t2 : ifon_) (vh vh1 vh2 : val_hat) :
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      mMapsTo l vh C ->         
      (<{C, R}> ⊨ (ilab t1 l1)) ->
      (<{C, R}> ⊨ (ilab t2 l2)) ->
      (* Caveat: In this case, we cannot assert that [t'] is structually smaller
         than [t1] or [t2]. Thus, this relation should be coinductively defined
         (i.e. we are define it on infinity).  
       *)
      (forall (x : var) (t' : fon_) (l' lf : label) (vh' vhx : val_hat),
          Subset (singleton (ilab (ifon__fun x (lab t' l')) lf)) vh1 ->
          mMapsTo x vhx R ->
          ((<{C, R}> ⊨ (inj (lab t' l'))) /\
           (Subset vh2 vhx) /\
           (Subset vh' vh))) ->
      (forall (f x : var) (t' : fon_) (l' lf : label) (vh' vhf vhx : val_hat),
          Subset (singleton (ilab (ifon__fix f x (lab t' l')) lf)) vh1 ->
          mMapsTo x vhx R ->
          mMapsTo f vhf R ->        
          Subset (singleton (ilab (ifon__fix f x (lab t' l')) lf)) vhf /\
          ((<{C, R}> ⊨ inj (lab t' l')) /\
           (Subset vh2 vhx) /\
           (Subset vh' vh)))  ->
      <{C, R}> ⊨ (ilab (ifon__app (ilab t1 l1) (ilab t2 l2)) l)
  | a__if (l l0 l1 l2 : label) (t0 t1 t2 : ifon_) (vh vh1 vh2 : val_hat):
      mMapsTo l vh C ->
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      (<{C, R}> ⊨ (ilab t0 l0)) ->  
      (<{C, R}> ⊨ (ilab t1 l1)) ->
      (<{C, R}> ⊨ (ilab t2 l2)) ->
      Subset vh1 vh ->
      Subset vh2 vh ->
      <{C, R}> ⊨ (ilab (ifon__if (ilab t0 l0) (ilab t1 l1) (ilab t2 l2)) l)
  | a__let (x : var) (l l1 l2 : label) (t1 t2 : ifon_) (vh vh1 vh2 vhx : val_hat):
      mMapsTo l vh C ->
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->
      mMapsTo x vhx R ->
      Subset vh2 vh ->
      Subset vh1 vhx ->  
      (<{C, R}> ⊨ (ilab t1 l1)) ->
      (<{C, R}> ⊨ (ilab t2 l2)) ->
      <{C, R}> ⊨ (ilab (ifon__let x (ilab t1 l1) (ilab t2 l2)) l)
  | a__op (t1 t2 : ifon_) (l l1 l2 : label) (o : op) :
      (<{C, R}> ⊨ (ilab t1 l1)) ->
      (<{C, R}> ⊨ (ilab t2 l2)) ->
      <{C, R}> ⊨ (ilab (ifon__op o (ilab t1 l1) (ilab t2 l2)) l)
  | a__bnd (l l0 : label) (r : env) (it0 : ifon_) (vh0 vh : val_hat):
      (<{C, R}> ⊨ ilab it0 l0) ->
      mMapsTo l0 vh0 C ->
      mMapsTo l vh C ->      
      Subset vh0 vh ->
      correct r R ->
      (<{C, R}> ⊨ ilab (ifon__bnd r (ilab it0 l0)) l)
  | a__cls (l : label) (r : env) (t0 : fon_) (vh : val_hat):
      mMapsTo l vh C ->      
      Subset (singleton (inj (lab t0 l))) vh ->
      correct r R ->
      (<{C, R}> ⊨ ilab (ifon__cls t0 r) l)
  where  "'<{' C ',' R '}>' '⊨' tl" := (analyse C R tl)
  .
  
  Module P := WProperties_fun(IFonl_as_OT)(SetIFonl).
  Import P.
  Theorem correctness_result :
    forall r R ie ie' C,
      correct r R ->
      (r ⊢ ie ---> ie') ->
      (<{C, R}> ⊨ ie) -> 
      (<{C, R}> ⊨ ie').
  Proof.
    intros.
    induction H0; inversion H1; clear H1; subst; inversion H; clear H; subst. 
    - unfold inj_ival. destruct v.
      + eapply a__cls.
        * apply H5.
        * eapply subset_trans; try apply H6.
  Admitted.

  Theorem analysis_inclusion :
    forall C R l1 l2 it1 it2 vh1 vh2,
      (<{C, R}> ⊨ (ilab it1 l1)) ->
      mMapsTo l1 vh1 C ->
      mMapsTo l2 vh2 C ->       
      Subset vh1 vh2 ->
      (<{C, R}> ⊨ (ilab it2 l2)).
  Admitted.

  (** ** Existence of the Solution *)
  (** In [PoPA], this is achieved by defining a complete lattice
  
          L = (L, ⊑) where L is (̂C, ̂R)

      and prove they are Moore Families so that the lfp existence comes for
      free. But, I don't have time to formalize a lattice here.

      This section is left blank.

   *)  

End AnalysisI.


