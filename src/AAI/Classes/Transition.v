Require Import FP.Classes.Monad.
Require Import FP.Core.

Class Transition (ss:qtype -> qtype) m `{! Monad m } :=
  { transition : forall {A B}, dom ((A ⇒ m B) ⇒ (ss A ⇒ ss B)) }.