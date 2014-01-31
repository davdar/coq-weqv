Require Import NoQ.Equivalence.

Class Eqv A :=
  { eqv : A -> A -> Prop
  ; Eqv_Equivalence :> Equivalence eqv
  }.
Infix "≃" := eqv (at level 70, no associativity).