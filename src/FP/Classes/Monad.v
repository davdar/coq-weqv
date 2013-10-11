Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Unit.

Import WeakEqv.Notation.
Import WeakSetoid.Notation.
Import Unit.Notation.

Class Monad (m:WeakSetoid -> WeakSetoid) : Type :=
  { ret : 
      forall {A:WeakSetoid}, 
      DD (A ⇨ m A)
  ; bind : forall {A B:WeakSetoid}, 
      DD (m A ⇨ (A ⇨ m B) ⇨ m B)
  ; monad_left_unit : 
      forall {A:WeakSetoid} (xM:DD (m A)), 
      bind ⊛ xM ⊛ ret ≈ xM
  ; monad_right_unit : 
      forall {A B:WeakSetoid} (x:DD A) (k:DD (A ⇨ m B)), 
      bind ⊛ (ret ⊛ x) ⊛ k ≈ k ⊛ x
  }.

Class MonadState (S:WeakSetoid) (m:WeakSetoid -> WeakSetoid) : Type :=
  { get : DD (m S)
  ; put : DD (S ⇨ m (EL ⊤))
  }.

Class MonadPlus (m:WeakSetoid -> WeakSetoid) `{! Monad m } : Type :=
  { mplus : 
      forall {A:WeakSetoid}, 
      DD (m A ⇨ m A ⇨ m A) 
  ; monad_plus_distributivity : 
      forall {A B:WeakSetoid} (xM yM:DD (m A)) (k:DD (A ⇨ m B)), 
      bind ⊛ (mplus ⊛ xM ⊛ yM) ⊛ k ≈ mplus ⊛ (bind ⊛ xM ⊛ k) ⊛ (bind ⊛ yM ⊛ k)
  }.