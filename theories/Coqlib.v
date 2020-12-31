(** * Coqlib : Tame the Annoyance in Coq Stdlib   *)

From Coq Require Export String.
From Coq Require Export Lists.List.
From Coq Require Export ZArith. 
From Coq Require Export FSetAVL. From Coq Require Export FMapAVL.
From Coq Require Export OrderedTypeEx OrderedType DecidableType.
From Coq Require Export FSetWeakList FMapWeakList FSetProperties.
From Coq Require Export Logic.
From QuickChick Require Import QuickChick.
Require Export ExtLib.Structures.Monads.


(* Reference: TImp *)

Ltac solve_right := 
  let Contra := fresh "Contra" in
  try solve [right; intro Contra; inversion Contra; subst; 
             clear Contra; eauto; congruence].

Ltac solve_left  := try solve [left; econstructor; eauto].


(** tactics to solve basic decidability branching   *)
Ltac solve_intui :=
  try solve[left; intuition; auto];
  try solve[left; constructor; intuition; auto].
Ltac solve_contra :=
  try solve[right; intros Contra; inversion Contra; auto].

Ltac solve_dec :=
  solve_intui;
  solve_contra.

