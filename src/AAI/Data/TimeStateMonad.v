Require Import FP.Core.
Require Import FP.Data.Product.
Require Import FP.Classes.Monad.
Require Import AAI.Classes.MonadTimeState.

Inductive v_timeStateMonadT (t:qtype) (m:qtype -> qtype) (a:qtype) :=
  v_TimeStateMonadT
  { v_unTimeStateMonadT : dom (t ⇒ m (a × t)) }.
Arguments v_TimeStateMonadT {t m a} _.
Arguments v_unTimeStateMonadT {t m a} _.

Instance : forall t m a, Eqv (v_timeStateMonadT t m a) :=
  { eqv x y := eqv (v_unTimeStateMonadT x) (v_unTimeStateMonadT y) }.
Proof.
  constructor ; simpl ; intros.
  - LibReflexivity.
  - Symmetry ; auto.
  - Transitivity (v_unTimeStateMonadT y) ; auto.
Defined.

Instance : forall t m a, Lte (v_timeStateMonadT t m a) :=
  { lte x y := lte (v_unTimeStateMonadT x) (v_unTimeStateMonadT y) }.
Proof.
  constructor ; simpl ; intros.
  - Reflexivity ; auto.
  - Transitivity (v_unTimeStateMonadT y) ; auto.
Defined.

Definition timeStateMonadT t m a : qtype :=
  {| qdom := v_timeStateMonadT t m a |}.

Definition TimeStateMonadT {t m a} : dom ((t ⇒ m (a × t)) ⇒ timeStateMonadT t m a) := qλ f → (v_TimeStateMonadT f : dom (timeStateMonadT t m a)).

Definition timeStateMonadT_ret {t m a} `{! Monad m } 
: dom (a ⇒ timeStateMonadT t m a) :=
  qλ a → TimeStateMonadT ∙ (qλ t → ret ∙ (a ,, t)).

Instance : forall t m, Monad (timeStateMonadT t m) :=
  { 

Instance : forall t m, MonadTimeState t (TimeStateMonadT t m).