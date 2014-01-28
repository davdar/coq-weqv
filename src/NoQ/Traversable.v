Require Import NoQ.Monad.

Class Traversable (t:Type -> Type) :=
  { tsequence : forall {m:Type->Type} `{! Monad m } {A}, t (m A) -> m (t A) }.