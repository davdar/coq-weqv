Require Import NoQ.Monad.
Require Import NoQ.Function.

Class MonadState (S:Type) (m:Type -> Type) `{! Monad m } :=
  { mget : m S
  ; mput : S -> m unit
  }.

Section MonadState.
  Context {S m} `{! Monad m ,! MonadState S m }.

  Definition mmodify (f:S -> S) : m unit :=
    s <- mget ;;
    mput $ f s.
End MonadState.