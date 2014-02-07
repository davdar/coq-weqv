Require Import NoQ.PreOrder.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Symmetric.
Require Import NoQ.Eqv.

Class PartialOrder A `{! Eqv A ,! PreOrder A } :=
  { PartialOrder_Antisymmetric :> Antisymmetric lte
  }.
