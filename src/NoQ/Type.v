Require Import NoQ.Universe.
Require Import NoQ.Eqv.

Infix "×" := (prod : Type -> Type -> Type) (left associativity, at level 40).
Instance Type_Universe : Universe Type :=
  { dom A := A }.
Instance Type_UHasEqv : UHasEqv Type :=
  { UHasEqv_Eqv A := Lib_Eqv A }.