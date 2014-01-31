Require Import NoQ.Reflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.

Class Equivalence {A} (R:A -> A -> Prop) :=
  { Equivalence_Reflexive :> Reflexive R
  ; Equivalence_Symmetric :> Symmetric R
  ; Equivalence_Transitive :> Transitive R
  }.
