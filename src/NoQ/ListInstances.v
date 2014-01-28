Require Import NoQ.Monad.
Require Import NoQ.Traversable.
Require Import NoQ.List.
Require Import NoQ.Function.

Fixpoint list_tsequence {m} `{! Monad m } {A} (xUs:list (m A)) : m (list A) :=
  match xUs with
  | [] => ret []
  | xM::xMs => 
      x <- xM ;;
      monad_map (cons x) $ list_tsequence xMs
  end.
Instance List_Traversable : Traversable list :=
  { tsequence := @list_tsequence }.