Require Import NoQ.WeakEquivalence.

Class Antisymmetric {A} 
(eqv:A -> A -> Prop) `{! WeakEquivalence eqv } 
(R:A -> A -> Prop) :=
  { antisymmetry : forall {x y}, R x y -> R y x -> eqv x y }.