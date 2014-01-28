Require Import NoQ.List.
Require Import NoQ.Function.

Class Monad (m:Type -> Type) :=
  { ret : forall {A}, A -> m A
  ; bind : forall {A B}, m A -> (A -> m B) -> m B
  }.

Infix ">>=" := bind (at level 50, left associativity).
Notation "a =<< b" := (bind b a) (at level 60, right associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).

Section Monad.
  Context {m} `{! Monad m }.
  
  Definition seq {A B} (xM:m A) (yM:m B) : m B := xM >>= fun _ => yM.

  Definition list_mapM {A B} (f:A -> m B) := fix self (xs:list A) : m (list B) :=
      match xs with
      | [] => ret []
      | x::xs =>
          y <- f x ;;
          ys <- self xs ;;
          ret $ y::ys
      end.
  
  Definition monad_map {A B} (f:A -> B) (xM:m A) : m B :=
    x <- xM ;;
    ret $ f x.
End Monad.

Infix ">>" := seq (at level 50, left associativity).
Notation "e1 ;; e2" := (seq e1 e2)
  (at level 100, right associativity).
