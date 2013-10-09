Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Unit.

Import WeakEqv.Notation.
Import WeakSetoid.Notation.
Import Unit.Notation.

Class Monad (m:WeakSetoid -> WeakSetoid) : Type :=
  { ret : forall {A:WeakSetoid}, DD (A ⇨ m A)
  ; bind : forall {A B:WeakSetoid}, DD (m A ⇨ (A ⇨ m B) ⇨ m B)
  ; monad_left_unit : forall {A:WeakSetoid} (xM:DD (m A)), bind ⊛ xM ⊛ ret ≈ xM
  ; monad_right_unit : forall {A B:WeakSetoid} (x:DD A) (k:DD (A ⇨ m B)), bind ⊛ (ret ⊛ x) ⊛ k ≈ k ⊛ x
  }.

Class MonadState (S:WeakSetoid) (m:WeakSetoid -> WeakSetoid) : Type :=
  { get : DD (m S)
  ; put : DD (D ⇨ m ⊤)