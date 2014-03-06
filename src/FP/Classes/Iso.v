Require Import FP.Core.

Class Iso A B :=
  { isoTo : dom (A ⇒ B)
  ; isoFrom : dom (B ⇒ A)
  ; iso_to_from : (isoTo ⊙ isoFrom) ≃ id
  ; iso_from_to : (isoFrom ⊙ isoTo) ≃ id
  }.