Require Import FP.Core.
Require Import FP.Data.Product.
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
Arguments unStateMonadT : simpl never.
Instance : forall S m A, Injection (@unStateMonadT S m A) :=
  { injection _x _y p := p }.
Global Opaque StateMonadT.
Global Opaque unStateMonadT.
Definition StateMonadT_inv {S m A} (f:dom (S ⇒ m (A × S))) 
: (@unStateMonadT S m A) ∙ (StateMonadT ∙ f) ≃ f := libReflexivity f.
Ltac StateMonadRewrite :=
  match goal with
  |- ⟨ unStateMonadT ∙ (StateMonadT ∙ ?f) ∈ _ ⋈ _ ⟩ => ReplaceBy (StateMonadT_inv f)
  end.
  
Definition runStateMonadT {S m A} : dom (S ⇒ stateMonadT S m A ⇒ m (A × S)) :=
  λ x aM → unStateMonadT ∙ aM ∙ x.

Definition stateMonadT_ret {S m} `{! Monad m } {A} : dom (A ⇒ stateMonadT S m A) :=
  λ a → StateMonadT $ λ s → ret ∙ (a ,, s).
Definition stateMonadT_bind {S m} `{! Monad m } {A B}
: dom (stateMonadT S m A ⇒ (A ⇒ stateMonadT S m B) ⇒ stateMonadT S m B) :=
  λ aM k → StateMonadT $ λ s →
    axs ← runStateMonadT ∙ s ∙ aM ;;
    prod_elim ∙ axs $ λ a s →
    runStateMonadT ∙ s ∙ (k ∙ a).
    
Instance : forall S m `{! Monad m }, Monad (stateMonadT S m) :=
  { ret := @stateMonadT_ret S m _
  ; bind := @stateMonadT_bind S m _
  }.
Proof.
  Local Ltac Hammer := 
    repeat
      (Re fail || ProdRewrite || MonadRewrite || StateMonadRewrite ; qproper_elim).
  - intros ; simpl.
    apply (injection unStateMonadT).
    Hammer.
    Transitivity (bind ∙ (unStateMonadT ∙ aM ∙ y) ∙ ret) ; qproper_elim ; Hammer.
  - intros ; simpl.
    apply (injection unStateMonadT).
    Hammer.
  - intros ; simpl.
    Hammer.
Defined.