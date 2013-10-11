Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.

Class Eqv (A:Type) : Type :=
  { eqv : A -> A -> Type
  ; Eqv_Reflexive :> Reflexive eqv
  ; Eqv_Symmetric :> Symmetric eqv
  ; Eqv_Transitive :> Transitive eqv
  }.
Arguments eqv {A} {Eqv} _ _ : simpl never.

Module Notation.
  Infix "≃" := eqv (no associativity, at level 70).
End Notation.