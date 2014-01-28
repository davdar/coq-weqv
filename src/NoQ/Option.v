Require Import NoQ.Function.
Require Import NoQ.Monad.

Arguments None {A}.
Arguments Some {A} _.

Definition option_ret {A} : A -> option A := Some.
Definition option_bind {A B} (aM:option A) (f:A -> option B) : option B :=
  match aM with
  | None => None
  | Some a => f a
  end.
Instance Option_Monad : Monad option :=
  { ret := @option_ret
  ; bind := @option_bind
  }.