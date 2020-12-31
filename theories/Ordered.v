From CFA Require Export Lang.
From CFA Require Export Coqlib.

(** * Ordered : Ordered Types Modules *)

(** Caveat: This chapter is extremely frsutrating and annoying *)

Definition Fonl_compare (x y : fon_l) : comparison :=
  Z.compare (lab_of x) (lab_of y).

Definition Fonl_equal (x y : fon_l) : bool :=
  Z.eqb (lab_of x) (lab_of y).


(** ** Ordered fon_l Type Module *)
(** the ordering of [fon_l] depends on the [Z] ordering of [label] *)
Module Fonl_as_OT <: OrderedType.
  Definition t := fon_l.
  Definition eq (x y : t) := @eq Z (lab_of x) (lab_of y).

  Definition eq_refl : forall x : t, eq x x.
  Proof. intros. split. Qed. 

  Definition eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intuition. Qed.

  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq. intros. destruct x, y, z. intuition. Qed.

  Definition lt (x y : t) := Z.lt (lab_of x) (lab_of y).

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt. intros. destruct x, y, z. intuition. Qed.

  Definition lt_not_eq : forall x y : t, lt x y -> ~eq x y.
  Proof. unfold lt, eq. intros. destruct x, y. intuition. Qed.

  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    case_eq (Fonl_compare x y); intro.
    - apply EQ. now apply Z.compare_eq. 
    - apply LT. assumption.
    - apply GT. now apply Z.gt_lt.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. intros. destruct x, y. simpl. 
    apply Z_as_OT.eq_dec.
  Defined.
End Fonl_as_OT.



(* Test *)
Compute (Fonl_compare
          (lab (fon__id "x"%string) 2)
          (lab (fon__id "x"%string) 2)).
Compute (Fonl_as_OT.compare
          (lab (fon__id "x"%string) 2)
          (lab (fon__id "x"%string) 2)).
Compute (Z_as_OT.compare 2 3).

Definition IFonl_compare (x y : ifon_l) : comparison :=
  Z.compare (ilab_of x) (ilab_of y).

Definition IFonl_equal (x y : ifon_l) : bool :=
  Z.eqb (ilab_of x) (ilab_of y).

Module IFonl_as_OT <: OrderedType.
  Definition t := ifon_l.
  Definition eq (x y : t) := @eq Z (ilab_of x) (ilab_of y).

  Definition eq_refl : forall x : t, eq x x.
  Proof. intros. split. Qed. 

  Definition eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intuition. Qed.

  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq. intros. destruct x, y, z. intuition. Qed.

  Definition lt (x y : t) := Z.lt (ilab_of x) (ilab_of y).

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt. intros. destruct x, y, z. intuition. Qed.

  Definition lt_not_eq : forall x y : t, lt x y -> ~eq x y.
  Proof. unfold lt, eq. intros. destruct x, y. intuition. Qed.

  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    case_eq (IFonl_compare x y); intro.
    - apply EQ. now apply Z.compare_eq. 
    - apply LT. assumption.
    - apply GT. now apply Z.gt_lt.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. intros. destruct x, y. simpl. 
    apply Z_as_OT.eq_dec.
  Defined.
End IFonl_as_OT.


(* Map Modules *)
Module MapString_ := FMapAVL.Make(String_as_OT).
Module MapZ_ := FMapAVL.Make(Z_as_OT).

Module MapLabel_ := MapZ_.      (* todo: Notation  *)

(* Set Modules *)
Module SetFonl := FSetAVL.Make(Fonl_as_OT).
Module PSetFonl := FSetAVL.Make(SetFonl).
Module SetIFonl := FSetAVL.Make(IFonl_as_OT).
Module PSetIFonl := FSetAVL.Make(SetIFonl).
