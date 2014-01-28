Require Import NoQ.Monad.

Class MonadFail (m:Type -> Type) `{! Monad m } :=
  { fail : forall {A}, m A
  ; try : forall {A}, m A -> m A -> m A
  }.