Require Import NoQ.Eqv.
Require Import NoQ.Relation.

Class Antisymmetric {A} `{! Eqv A } (R:relation A) :=
  { antisymmetry : forall {x y}, R x y -> R y x -> x ≃ y }.