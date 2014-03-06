Require Import FP.Core.
Require Import FP.Data.Product.
Require Import FP.Data.Unit.
Require Import FP.Classes.Monad.
Require Import FP.Classes.Injection.

Inductive v_stateMonadT (S:qtype) (m:qtype -> qtype) (A:qtype) :=
  v_StateMonadT
  { v_unStateMonadT : dom (S ⇒ m (A × S)) }.
Arguments v_StateMonadT {S m A} _.
Arguments v_unStateMonadT {S m A} _.

Definition stateMonadT S m A := derive (v_stateMonadT S m A) v_unStateMonadT.

Definition StateMonadT {S m A} : dom ((S ⇒ m (A × S)) ⇒ stateMonadT S m A) :=
  λ f → (v_StateMonadT f : dom (stateMonadT S m A)).
Definition unStateMonadT {S m A} : dom (stateMonadT S m A ⇒ S ⇒ m (A × S)) :=
  λ aM → v_unStateMonadT (aM : dom (stateMonadT S m A)).
Instance : forall S m A, InjectionEqv (@unStateMonadT S m A) :=
  { injectionEqv _x _y p := p }.
Instance : forall S m A, InjectionLte (@unStateMonadT S m A) :=
  { injectionLte _x _y p := p }.
Global Opaque StateMonadT.
Global Opaque unStateMonadT.
Definition StateMonadT_inv {S m A} (f:dom (S ⇒ m (A × S))) 
: unStateMonadT ∙ (StateMonadT ∙ f) ≃ f := libReflexivity.
Ltac StateMonadRewrite :=
  match goal with
  |- ⟨ unStateMonadT ∙ (StateMonadT ∙ ?f) ∈ _ |_| _ ⟩ => ReplaceBy (StateMonadT_inv f)
  end.

Section StateMonadT.
  Context {S:qtype} {m:qtype -> qtype} `{! Monad m }.

  Definition runStateMonadT {A} : dom (S ⇒ stateMonadT S m A ⇒ m (A × S)) :=
    λ x aM → unStateMonadT ∙ aM ∙ x.

  Definition stateMonadT_ret {A} : dom (A ⇒ stateMonadT S m A) :=
    λ a → StateMonadT $ λ s → ret ∙ (a ,, s).
  Definition stateMonadT_bind {A B}
  : dom (stateMonadT S m A ⇒ (A ⇒ stateMonadT S m B) ⇒ stateMonadT S m B) :=
    λ aM k → StateMonadT $ λ s →
      axs ← runStateMonadT ∙ s ∙ aM ;;
      prod_elim ∙ axs $ λ a s →
      runStateMonadT ∙ s ∙ (k ∙ a).

  Global Instance : Monad (stateMonadT S m) :=
    { ret := @stateMonadT_ret
    ; bind := @stateMonadT_bind
    }.
  Proof.
    Local Ltac Hammer := 
      repeat
        (Re fail || ProdRewrite || MonadRewrite || StateMonadRewrite ; qproper_elim).
    - intros ; simpl.
      apply (injectionEqv unStateMonadT).
      Hammer.
      Transitivity (bind ∙ (unStateMonadT ∙ aM ∙ y) ∙ ret) ; qproper_elim ; Hammer.
    - intros ; simpl.
      apply (injectionEqv unStateMonadT).
      Hammer.
    - intros ; simpl.
      Hammer.
  Defined.

  Definition stateMonadT_get : dom (stateMonadT S m S) :=
    StateMonadT $ λ s → ret ∙ (s ,, s).
  Definition stateMonadT_put : dom (S ⇒ stateMonadT S m unit) :=
    λ s → StateMonadT $ λ _ → ret ∙ (tt ,, s).
  Global Instance : MonadState S (stateMonadT S m) :=
    { get := stateMonadT_get
    ; put := stateMonadT_put
    }.
End StateMonadT.