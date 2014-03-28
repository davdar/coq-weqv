Require Import FP.Core.
Require Import FP.Data.Stream.
Require Import FP.Data.Nat.

Class Compat (t:qtype -> qtype) := { compat : qtype -> Prop }.
Arguments compat t {Compat} _.

Class Sequence t `{! Compat t } :=
  { toStream : forall {A}, compat t A -> dom (t A ⇒ stream A) 
  ; fromStream : forall {A}, compat t A -> dom (stream A ⇒ t A)
  ; length : forall {A}, compat t A -> dom (stream A ⇒ nat)
  }.