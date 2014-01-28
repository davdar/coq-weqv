Require Import NoQ.Monad.
Require Import NoQ.Function.
Require Import NoQ.DecEq.
Require Import NoQ.MonadPlus.
Require Import NoQ.List.

Definition Store (D:Type -> Type) (L:Type) (V:Type) := list (L * D V).

Class MonadStoreState D L V (m:Type -> Type) :=
  { getStore : m (Store D L V)
  ; putStore : Store D L V -> m unit
  }.

Section MonadStoreState.
  Context {D L V m} `{! Monad m ,! MonadStoreState D L V m }.

  Definition modifyStore (f:Store D L V -> Store D L V) : m unit :=
    e <- getStore ;;
    putStore $ f e.

  Definition lookupStore `{! DecEq L ,! MonadPlus m } (n:L) : m (D V) := mplusFromOption =<< monad_map (lookup n) getStore.
End MonadStoreState.