Require Import FP.Core.
Require Import FP.Data.Product.
Require Import FP.Data.Unit.
Require Import FP.Data.StateMonad.
Require Import FP.Classes.Monad.
Require Import FP.Classes.Injection.
Require Import FP.Classes.ProperFunctor.
Require Import FP.Classes.Galois.
Require Import AAI.Classes.MonadTimeState.
Require Import AAI.Classes.Transition.

Inductive v_timeStateMonadT (T:qtype) (m:qtype -> qtype) (A:qtype) :=
  v_TimeStateMonadT
  { v_unTimeStateMonadT : dom (stateMonadT T m A) }.
Arguments v_TimeStateMonadT {T m A} _.
Arguments v_unTimeStateMonadT {T m A} _.

Definition timeStateMonadT T m A := derive (v_timeStateMonadT T m A) v_unTimeStateMonadT.

Definition TimeStateMonadT {T m A} : dom (stateMonadT T m A ⇒ timeStateMonadT T m A) := 
  λ aM → v_TimeStateMonadT aM : dom (timeStateMonadT T m A).
Definition unTimeStateMonadT {T m A} : dom (timeStateMonadT T m A ⇒ stateMonadT T m A) :=
  λ aM → (v_unTimeStateMonadT : dom (timeStateMonadT T m A) -> _) aM.
Instance : forall T m A, InjectionEqv (@unTimeStateMonadT T m A) :=
  { injectionEqv _x _y p := p }.
Instance : forall T m A, InjectionLte (@unTimeStateMonadT T m A) :=
  { injectionLte _x _y p := p }.
Global Opaque TimeStateMonadT.
Global Opaque unTimeStateMonadT.
Definition TimeStateMonadT_inv {T m A} (aM:dom (stateMonadT T m A))
: unTimeStateMonadT ∙ (TimeStateMonadT ∙ aM) ≃ aM := libReflexivity.
Ltac TimeStateMonadRewrite :=
  match goal with
  |- ⟨ unTimeStateMonadT ∙ (TimeStateMonadT ∙ ?aM) ∈ _ |_| _ ⟩ => ReplaceBy (TimeStateMonadT_inv aM)
  end.
  
Section TimeStateMonadT.
  Context {T:qtype} {m} `{! Monad m }.

  Definition runTimeStateMonadT {A} : dom (T ⇒ timeStateMonadT T m A ⇒ m (A × T)) :=
    λ t → runStateMonadT ∙ t ⊙ unTimeStateMonadT.
  
  Definition timeStateMonadT_ret {A} : dom (A ⇒ timeStateMonadT T m A) :=
    λ a → TimeStateMonadT $ (ret ∙ a : dom (stateMonadT T m A)).
  Definition timeStateMonadT_bind {A B} 
  : dom (timeStateMonadT T m A ⇒ (A ⇒ timeStateMonadT T m B) ⇒ timeStateMonadT T m B) :=
    λ aM f → TimeStateMonadT ∙ ( 
      a ← unTimeStateMonadT ∙ aM ;;
      unTimeStateMonadT $ f ∙ a).
  Global Instance : Monad (timeStateMonadT T m) :=
    { ret := @timeStateMonadT_ret
    ; bind := @timeStateMonadT_bind
    }.
  Proof.
    Local Ltac Hammer :=
      repeat 
        (Re fail || MonadRewrite || TimeStateMonadRewrite ; qproper_elim).
    - simpl ; intros.
      apply (injectionEqv unTimeStateMonadT) ; Hammer.
      Transitivity (bind ∙ (unTimeStateMonadT ∙ aM) ∙ ret) ; qproper_elim ; Hammer.
    - simpl ; intros.
      apply (injectionEqv unTimeStateMonadT) ; Hammer.
    - simpl ; intros ; Hammer.
  Defined.
  
  Definition timeStateMonadT_getTime : dom (timeStateMonadT T m T) :=
    TimeStateMonadT $ get.
  Definition timeStateMonadT_putTime : dom (T ⇒ timeStateMonadT T m unit) :=
    λ t → TimeStateMonadT $ put ∙ t.
  Global Instance : MonadTimeState T (timeStateMonadT T m) :=
    { getTime := @timeStateMonadT_getTime
    ; putTime := @timeStateMonadT_putTime
    }.
  
  Context `{! Transition m }.

  Definition timeStateMonadT_ss A := ss m (A × T).
  Definition timeStateMonadT_transition {A B} 
  : dom ((A ⇒ timeStateMonadT T m B) ⇒ (timeStateMonadT_ss A ⇒ timeStateMonadT_ss B)) :=
    λ f → transition $ λ axt → 
     prod_elim ∙ axt $ λ a t → 
       runTimeStateMonadT ∙ t ∙ (f ∙ a).

  Global Instance : Transition (timeStateMonadT T m) :=
    { ss := timeStateMonadT_ss
    ; transition := @timeStateMonadT_transition 
    }.
  
End TimeStateMonadT.

Section Galois.
  Context {T₁ m₁ T₂ m₂} 
  `{! Monad m₁ ,! Transition m₁ ,! Monad m₂ ,! Transition m₂ ,! Galois T₁ T₂ }.

  Section GaloisFunctor.
    Context `{! GaloisFunctor m₁ m₂ }.

    Definition timeStateMonadT_galoisα {A₁ A₂} `{! Galois A₁ A₂ } 
    : dom (timeStateMonadT T₁ m₁ A₁ ⇒ timeStateMonadT T₂ m₂ A₂) :=
      λ aM₁ → TimeStateMonadT $ StateMonadT $ λ t₂ →
          galoisα ∙ (runTimeStateMonadT ∙ (galoisγ ∙ t₂) ∙ aM₁).
    Definition timeStateMonadT_galoisγ {A₁ A₂} `{! Galois A₁ A₂ }
    : dom (timeStateMonadT T₂ m₂ A₂ ⇒ timeStateMonadT T₁ m₁ A₁) :=
      λ aM₂ → TimeStateMonadT $ StateMonadT $ λ t₁ →
          galoisγ ∙ (runTimeStateMonadT ∙ (galoisα ∙ t₁) ∙ aM₂).
    Local Instance 
    : forall A₁ A₂, Galois A₁ A₂ -> Galois (timeStateMonadT T₁ m₁ A₁) (timeStateMonadT T₂ m₂ A₂) :=
      { galoisα := timeStateMonadT_galoisα
      ; galoisγ := timeStateMonadT_galoisγ
      }.
    Proof.
      Local Ltac Hammer := repeat 
        (Re fail || GaloisRewrite || StateMonadRewrite || TimeStateMonadRewrite ; qproper_elim).
      - Hammer.
        apply (injectionLte unTimeStateMonadT) ; Hammer.
        apply (injectionLte unStateMonadT) ; Hammer.
      - Hammer.
        apply (injectionLte unTimeStateMonadT) ; Hammer.
        apply (injectionLte unStateMonadT) ; Hammer.
    Defined.
    Global Instance : GaloisFunctor (timeStateMonadT T₁ m₁) (timeStateMonadT T₂ m₂) := {}.
  End GaloisFunctor.
  
  Section GaloisTransition.
    Context `{! GaloisTransition m₁ m₂ }.

    Local Instance
    : forall A₁ A₂, Galois A₁ A₂ -> 
      Galois (ss (timeStateMonadT T₁ m₁) A₁) (ss (timeStateMonadT T₂ m₂) A₂) :=
        { galoisα := galoisα (A:=ss m₁ (A₁ × T₁)) (B:=ss m₂ (A₂ × T₂))
        ; galoisγ := galoisγ : dom (ss m₂ (A₂ × T₂) ⇒ ss m₁ (A₁ × T₁))
        }.
    Proof.
      Local Ltac Hammer := repeat
        (Re fail || GaloisRewrite ; qproper_elim).
      - Hammer.
        apply qmonotonic_intro ; Hammer.
      - Hammer.
        apply qmonotonic_intro ; Hammer.
    Defined.
    Local Instance : GaloisFunctor (ss (timeStateMonadT T₁ m₁)) (ss (timeStateMonadT T₂ m₂)) := {}.
    Global Instance : GaloisTransition (timeStateMonadT T₁ m₁) (timeStateMonadT T₂ m₂) := {}.
  End GaloisTransition.
End Galois.