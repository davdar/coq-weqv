Require Import NoQ.Monad.
Require Import NoQ.Function.

Class MonadTimeState T (m:Type -> Type) :=
  { getTime : m T
  ; putTime : T -> m unit
  }.

Class Addressable L C T :=
  { tzero : T
  ; tnext : T -> T
  ; talloc : C -> T -> L
  }.

Section MonadTimeState.
  Context {T m} `{! Monad m ,! MonadTimeState T m }.

  Definition modifyTime (f:T -> T) : m unit :=
    e <- getTime ;;
    putTime $ f e.
  
  Context {C L} `{! Addressable L C T }.
  
  Definition alloc (c:C) : m L :=
    t <- getTime ;;
    putTime $ tnext t ;;
    ret $ talloc c t.
End MonadTimeState.