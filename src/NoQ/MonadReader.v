Require Import NoQ.Monad.

Class MonadReader (R:Type) (m:Type -> Type) `{! Monad m } :=
  { ask : m R
  ; local : forall A, (R -> R) -> m A -> m A
  }.