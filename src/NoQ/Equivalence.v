Require Import NoQ.LibReflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.

Class Equivalence {A} (R:A -> A -> Prop) :=
  { Equivalence_LibReflexive :> LibReflexive R
  ; Equivalence_Symmetric :> Symmetric R
  ; Equivalence_Transitive :> Transitive R
  }.
