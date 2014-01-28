Require Import NoQ.Monad.

Class MonadPlus (m:Type -> Type) `{! Monad m } :=
  { mzero : forall {A}, m A
  ; mplus : forall {A}, m A -> m A -> m A
  }.

Infix "<|>" := mplus (at level 60, right associativity).

Section MonadPlus.
  Context {m} `{! Monad m ,! MonadPlus m }.
  Definition mplusFromOption {A} (xM:option A) : m A :=
    match xM with
    | None => mzero
    | Some x => ret x
    end.
End MonadPlus.