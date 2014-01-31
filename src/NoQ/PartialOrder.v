Require Import NoQ.PreOrder.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Symmetric.
Require Import NoQ.WEqv.

Class PartialOrder A `{! WEqv A } :=
  { PartialOrder_PreOrder :> PreOrder A
  ; PartialOrder_Antisymmetric :> Antisymmetric weqv lte
  }.

Instance Function_PartialOrder 
{A} `{! WEqv A ,! PartialOrder A }
{B} `{! WEqv B ,! PartialOrder B }
: PartialOrder (A -> B) := {}.
Proof.
  constructor ; intros ; logical_intro.
  apply antisymmetry.
  - apply H ; logical_weqv.
  - apply H0 ; logical_weqv.
Defined.