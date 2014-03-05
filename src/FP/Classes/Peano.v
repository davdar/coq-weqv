Require Import FP.Core.

Class Peano (τ:qtype) :=
  { pzero : dom τ
  ; psucc : dom (τ ⇒ τ)
  }.