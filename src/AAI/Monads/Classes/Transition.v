Require Import NoQ.Monad.

Class Transition (ss:Type -> Type) (m:Type -> Type) `{! Monad m } :=
  { transition : forall {A B}, (A -> m B) -> ss A -> ss B
  }.