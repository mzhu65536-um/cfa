From CFA Require Export Coqlib.
From CFA Require Export Lang.
From CFA Require Export Ordered.

(** * Typeclasses : Encoding Modules as Typeclasses*)
(** Encapsulate Module Map, Set definition into Typeclasses *)
Class CMap (K V M : Type)  :=
  {
  mequal : M -> M -> bool;
  madd : K -> V -> M -> M;
  mfind : K -> M -> (option V);
  mMapsTo : K -> V -> M -> Prop;
  mremove : K -> M -> M;
  mmt : M
  }
.

Class CSet (K M : Type)  :=
  {
  ssingle : K -> M;
  selements : M -> list K;
  seq : M -> M -> Prop;
  seq_trans (s s' s'' : M) : seq s s' -> seq s' s'' -> seq s s'';
  sadd : K -> M -> M;
  sunion : M -> M -> M;
  ssubset : M -> M -> bool;
  sfor_all : (K -> bool) -> M -> bool;
  sfold {A : Type} : (K -> A -> A) -> M  -> A -> A;
  smt : M;
  sequal : M -> M -> bool;
  schoose : M -> (option K);
  sremove : K -> M -> M;
  seq_dec (s s' : M) : {seq s s'}+{~seq s s'}
  }
.


(** ̂ {Val} :: P(λl)  *)
Definition val_hat : Type := SetFonl.t. 

(** ̂ {Env} :: String -> ^{Val} *)
Definition env_hat : Type := MapString_.t val_hat.
(* Definition env : Type := MapString_.t fon_l. *)

(** ̂ {Cache} :: Label -> ^{Val} *)
Definition cache_hat : Type := MapLabel_.t val_hat.
Definition cache : Type := MapLabel_.t fon_l.


(** ** Intermezzo : Using Typeclasses as a Shortcut to Modules  *)
(** Writing things like [MapString_.add] is extremely painful, here we
    abstract map and set modules into typeclass to take the advatage
    of automatic inference.
 *)

Instance ValHatSet : CSet fon_l SetFonl.t :=
  {
  ssingle := SetFonl.singleton;
  selements := SetFonl.elements;
  sadd := SetFonl.add;
  sunion := SetFonl.union;
  smt := SetFonl.empty;
  ssubset := SetFonl.subset;
  sfor_all := SetFonl.for_all;
  sfold := SetFonl.fold;
  seq := SetFonl.eq;
  seq_trans := SetFonl.eq_trans;
  sequal := SetFonl.equal;
  schoose := SetFonl.choose;
  sremove := SetFonl.remove;
  seq_dec := SetFonl.eq_dec
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


Module Bundle.
  Inductive bundle : Type :=
  (* r(s) *)
  | b_r (s : var)
  (* C(l) *)
  | b_c (l : label)
  (* {t} *)
  | b_t (t : fon_l)
  .
End Bundle.


(** * Decidable : DecidableTypes Modules *)
(** un autre tragedie et mecontentement  *)

Module Bundle_as_DT.
  Include Bundle.
  Definition t := bundle.
  Definition eq (x y : t) : Prop :=
    match x, y with
    | b_r s1, b_r s2 => eq s1 s2
    | b_c l1, b_c l2 => eq l1 l2
    | b_t t1, b_t t2 => Fonl_as_OT.eq t1 t2
    | _, _ => False
    end.

  Definition eq_refl (x : t) : eq x x.
  Proof with intuition. destruct x... Qed.

  Definition eq_sym (x y : t) : eq x y -> eq y x.
  Proof with intuition. destruct x, y... Qed.


  Definition eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof with intuition.
    destruct x, y, z; intuition; try inversion H; try inversion H0;
      try solve [eapply eq_trans; eauto].
  Qed.

  Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Proof with intuition.
    intros. destruct x as [a | a | a], y as [b | b | b]; try auto.
    - destruct (string_dec a b); solve_dec.
    - destruct (Z.eq_dec a b); solve_dec.
    - destruct (Fonl_as_OT.eq_dec a b); solve_dec.
  Defined.
    
End Bundle_as_DT.  

Module SetBundle := FSetWeakList.Make(Bundle_as_DT).

Import Bundle.

Inductive constraint : Type  :=
(* lhs ⊆ rhs *)
| con_sub (lhs rhs : bundle)
(* lhs → rhs *)
| con_imp (lhs rhs : constraint)
.

Module Constraint_as_DT <: DecidableType.
  Definition t := constraint.

  Inductive eq' : t -> t -> Prop :=
  | eq_sub lhs1 rhs1 lhs2 rhs2 :
      Bundle_as_DT.eq lhs1 lhs2 -> Bundle_as_DT.eq rhs1 rhs2 ->
      eq' (con_sub lhs1 rhs1) (con_sub lhs2 rhs2)
  | eq_imp lhs1 rhs1 lhs2 rhs2 :
      eq' lhs1 lhs2 -> eq' rhs1 rhs2 ->
      eq' (con_imp lhs1 rhs1) (con_imp lhs2 rhs2) .

  Definition eq : t -> t -> Prop := eq'.
  
  Definition eq_refl (x : t) : eq x x.
  Proof.
    induction x as [l r | l r].
    - constructor; apply Bundle_as_DT.eq_refl.
    - constructor; assumption.
  Qed.
  Hint Resolve eq_refl : core.  
  Hint Resolve Bundle_as_DT.eq_sym : core.
  Definition eq_sym : forall (x y : t), eq x y -> eq y x.
  Proof with intuition.
    intros x.
    induction x; destruct y; intros; try inversion H; subst; constructor...
    apply IHx1...
    apply IHx2...
  Qed.

  Hint Resolve Bundle_as_DT.eq_trans : core.  
  Definition eq_trans : forall (x y z : t), eq x y -> eq y z -> eq x z.
  Proof with eauto.
    unfold eq.
    intros. generalize dependent z.
    induction H; intros; destruct z; inversion H1; constructor; subst;
      intuition...
  Qed.

  Definition eq_dec : forall (x y : t), {eq x y} + {~ eq x y}.
  Proof with auto.
    intros x.
    induction x as [lhs rhs | lhs IHl rhs IHr];
      destruct y as [lhs0 rhs0 | lhs0 rhs0]; solve_dec.
    destruct (Bundle_as_DT.eq_dec lhs lhs0), (Bundle_as_DT.eq_dec rhs rhs0);
      solve_dec.
    destruct (IHl lhs0), (IHr rhs0); solve_dec.
  Defined.
End Constraint_as_DT.

(* A set of constraints *)
Module SetConstr := FSetWeakList.Make(Constraint_as_DT).

Definition constr : Type := SetConstr.t.


Instance ConstrSet : CSet constraint SetConstr.t :=
  {
  ssingle := SetConstr.singleton;
  selements := SetConstr.elements;
  sadd := SetConstr.add;
  sunion := SetConstr.union;
  smt := SetConstr.empty;
  ssubset := SetConstr.subset;
  sfor_all := SetConstr.for_all;
  sfold := SetConstr.fold;
  seq := SetConstr.eq;
  seq_trans := SetConstr.eq_trans;
  sequal := SetConstr.equal;
  schoose := SetConstr.choose;
  sremove := SetConstr.remove;
  seq_dec := SetConstr.eq_dec
  }
.

(** * Graph formulation *)

Module MapNodes := FMapWeakList.Make(Bundle_as_DT).


Definition gdata : Type := MapNodes.t val_hat.
Definition gedge : Type := MapNodes.t constr.
Definition gqueue : Type := SetBundle.t.


Instance GDataMap : CMap bundle val_hat (MapNodes.t val_hat) :=
  {
  mMapsTo := @MapNodes.MapsTo val_hat;
  mequal := MapNodes.equal sequal;
  madd k v m := @MapNodes.add val_hat k v m;
  mfind k m := @MapNodes.find val_hat k m;
  mremove k m := @MapNodes.remove val_hat k m;
  mmt := MapNodes.empty val_hat;
  }
.

Instance GEdgeMap : CMap bundle constr (MapNodes.t constr) :=
  {
  mMapsTo := @MapNodes.MapsTo constr;
  mequal := MapNodes.equal sequal;
  madd k v m := @MapNodes.add constr k v m;
  mfind k m := @MapNodes.find constr k m;
  mremove k m := @MapNodes.remove constr k m;
  mmt := MapNodes.empty constr;
  }
.

Instance QueueSet : CSet bundle SetBundle.t :=
  {
  ssingle := SetBundle.singleton;
  selements := SetBundle.elements;
  sadd := SetBundle.add;
  sunion := SetBundle.union;
  smt := SetBundle.empty;
  ssubset := SetBundle.subset;
  sfor_all := SetBundle.for_all;
  sfold := SetBundle.fold;
  seq := SetBundle.eq;
  seq_trans := SetBundle.eq_trans;
  sequal := SetBundle.equal;
  schoose := SetBundle.choose;
  sremove := SetBundle.remove;
  seq_dec := SetBundle.eq_dec
  }
.
