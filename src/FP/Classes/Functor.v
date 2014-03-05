Require Import FP.Core.

Class Functor (t:qtype -> qtype) :=
  { map : forall {A B}, dom ((A ⇒ B) ⇒ (t A ⇒ t B)) }.