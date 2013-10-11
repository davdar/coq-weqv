Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Unit.
Require Import FP.Data.Function.

Import WeakEqv.Notation.
Import Eqv.Notation.
Import WeakSetoid.Notation.
Import Unit.Notation.
Import Function.Notation.

Class Functor (t:WeakSetoid -> WeakSetoid) :=
  { fmap : 
      forall {A B:WeakSetoid}, 
      DD ((A ⇨ B) ⇨ (t A ⇨ t B)) 
  ; functor_identity : 
      forall {A:WeakSetoid}, 
      fmap ⊛ (idQ (A:=A)) ≃ idQ
  ; functor_composition : 
      forall {A B C:WeakSetoid} (g:DD (B ⇨ C)) (f:DD (A ⇨ B)), 
      fmap ⊛ (composeQ ⊛ g ⊛ f) ≃ composeQ ⊛ (fmap ⊛ g) ⊛ (fmap ⊛ f)
  }.