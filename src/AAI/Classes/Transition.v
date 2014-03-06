Require Import FP.Classes.Monad.
Require Import FP.Classes.Galois.
Require Import FP.Classes.ProperFunctor.
Require Import FP.Core.

Class Transition m `{! Monad m } :=
  { ss : qtype -> qtype
  ; transition : forall {A B}, dom ((A ⇒ m B) ⇒ (ss A ⇒ ss B)) 
  }.
Arguments ss m {Monad0 Transition} _.
Global Opaque ss.

Class GaloisTransition m₁ m₂ `{! Monad m₁ ,! Transition m₁ ,! Monad m₂ ,! Transition m₂ } :=
  { GaloisTransition_GaloisFunctor :> GaloisFunctor (ss m₁) (ss m₂) }.