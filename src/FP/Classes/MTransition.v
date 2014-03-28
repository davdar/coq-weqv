Require Import FP.Core.
Require Import FP.Classes.Monad.
Require Import FP.Classes.MGalois.

Class MTransition m :=
  { ss : qtype -> qtype
  ; transition : forall A B, dom ((A ⇒ m B) ⇒ ss A ⇒ ss B)
  ; transition_MGalois :> forall m' `{! Monad m' } A B, MGalois m' A B -> MGalois m' (ss A) (ss B)
  }.