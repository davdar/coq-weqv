Require Import FP.Data.Function_Q.
Require Import FP.Data.RewriteState.
Require Import FP.Data.WeakSetoid.

Import WeakSetoid.Notation.

Ltac R_id_Q_beta :=
  match goal with
  | [ |- RewriteState (id_Q ⊛ ?x) _ _ ] => ReplaceBy (id_Q_beta x)
  end.

Ltac R_compose_Q_beta :=
  match goal with
  | [ |- RewriteState (compose_Q ⊛ ?g ⊛ ?f ⊛ ?x) _ _ ] => ReplaceBy (compose_Q_beta g f x)
  end.

Ltac R_Function_beta := R_id_Q_beta || R_compose_Q_beta.