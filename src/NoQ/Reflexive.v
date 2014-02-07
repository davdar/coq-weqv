Require Import NoQ.Eqv.

Class Reflexive {A} `{! Eqv A } (R:A -> A -> Prop) :=
  { reflexivity : forall {x y}, x ≃ y -> R x y }.