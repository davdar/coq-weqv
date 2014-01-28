Require Import NoQ.Monad.
Require Import NoQ.Function.
Require Import NoQ.MonadPlus.
Require Import NoQ.List.
Require Import NoQ.DecEq.

Definition Env (N:Type) (A:Type) := list (N * A).

Class MonadEnvState (N A:Type) (m:Type -> Type) `{! Monad m } :=
  { getEnv : m (Env N A)
  ; putEnv : Env N A -> m unit
  }.

Section MonadEnvState.
  Context {N A m} `{! Monad m ,! MonadEnvState N A m }.

  Definition modifyEnv (f:Env N A -> Env N A) : m unit :=
    e <- getEnv ;;
    putEnv $ f e.
  
  Definition lookupEnv `{! DecEq N ,! MonadPlus m } (n:N) : m A := mplusFromOption =<< monad_map (lookup n) getEnv.
End MonadEnvState.