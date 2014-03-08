Require Import FP.Core.
Require Import FP.Data.Unit.

Class Monad (m:qtype -> qtype) :=
  { ret : forall {A}, dom (A ⇒ m A)
  ; bind : forall {A B}, dom (m A ⇒ (A ⇒ m B) ⇒ m B)
  ; bind_ret_kon : forall {A} (aM:dom (m A)), bind ∙ aM ∙ ret ≃  aM
  ; bind_ret_arg : forall {A B} (a:dom A) (k:dom (A ⇒ m B)), bind ∙ (ret ∙ a) ∙ k ≃ k ∙ a
  ; bind_associativity : forall {A B C} (aM:dom (m A)) (k₁:dom (A ⇒ m B)) (k₂:dom (B ⇒ m C)), 
      bind ∙ (bind ∙ aM ∙ k₁) ∙ k₂ ≃ bind ∙ aM ∙ (λ a → bind ∙ (k₁ ∙ a) ∙ k₂)
  }.
Global Opaque ret.
Global Opaque bind.

Notation "e >>= k" := (bind ∙ e ∙ k) (at level 90, right associativity).
Notation "x ← e₁  ;; e₂" := (bind ∙ e₁ ∙ (λ x → e₂)) 
  (at level 100, e₁ at next level, right associativity).

Ltac MonadRewrite :=
  match goal with
  | |- ⟨ ?aM >>= ret ∈ _ |_| _ ⟩ => ReplaceBy (bind_ret_kon aM)
  | |- ⟨ ret ∙ ?a >>= ?k ∈ _ |_| _ ⟩ => ReplaceBy (bind_ret_arg a k)
  | |- ⟨ bind ∙ (bind ∙ ?aM ∙ ?k₁) ∙ ?k₂ ∈ _ |_| _ ⟩ => ReplaceBy (bind_associativity aM k₁ k₂)
  end.

Section Monad.
  Context {m} `{! Monad m }.
  
  Definition extend {A B} : dom ((A ⇒ m B) ⇒ (m A ⇒ m B)) := λ f aM → bind ∙ aM ∙ f.

  Definition mcompose {A B C} : dom ((B ⇒ m C) ⇒ (A ⇒ m B) ⇒ (A ⇒ m C)) := λ g f a → 
    bind ∙ (f ∙ a) ∙ g.
  Definition mmap {A B} : dom ((A ⇒ B) ⇒ (m A ⇒ m B)) := λ f aM →
    a ← aM ;;
    ret $ f ∙ a.
  
  Definition seq {A B} : dom (m A ⇒ m B ⇒ m B) := λ aM bM → _ ← aM ;; bM.
  
  Definition kret {A B} : dom ((A ⇒ B) ⇒ (A ⇒ m B)) := λ f → ret ⊙ f.
End Monad.
Notation "k =<< e" := (extend ∙ k ∙ e) (at level 70, right associativity).
Notation "g m⊙ f" := (mcompose ∙ g ∙ f) (at level 60, right associativity).
Notation "e₁  ;; e₂" := (_ ← e₁ ;; e₂) (at level 100, right associativity).

Section Laws.
  Context {m} `{! Monad m }.

  Definition mcompose_associativity {A B C D} 
  (h:dom (C ⇒ m D)) (g:dom (B ⇒ m C)) (f:dom (A ⇒ m B)) : ((h m⊙ g) m⊙ f) ≃ (h m⊙ (g m⊙ f)).
  Proof.
    repeat (Re fail || MonadRewrite ; qproper_elim).
  Qed.

  Definition mcompose_left_unit {A B} (f:dom (A ⇒ m B)) : (ret m⊙ f) ≃ f.
  Proof.
    repeat (Re fail || MonadRewrite ; qproper_elim).
  Qed.
  
  Definition mcompose_right_unit {A B} (f:dom (A ⇒ m B)) : (f m⊙ ret) ≃ f.
  Proof.
    repeat (Re fail || MonadRewrite ; qproper_elim).
  Qed.
End Laws.

Global Opaque kret.
Global Opaque mcompose.

Ltac KleisliRewrite :=
  match goal with
  | |- ⟨ (?h m⊙ ?g) m⊙ ?f ∈ _ |_| _ ⟩ => ReplaceBy (mcompose_associativity h g f)
  | |- ⟨ ret m⊙ ?f ∈ _ |_| _ ⟩ => ReplaceBy (mcompose_left_unit f)
  | |- ⟨ ?f m⊙ ret ∈ _ |_| _ ⟩ => ReplaceBy (mcompose_right_unit f)
  end.

Ltac KleisliRewrite2 :=
  match goal with
  | |- ⟨ ?h m⊙ ?g m⊙ ?f ∈ _ |_| _ ⟩ => ReplaceBy (symmetry (mcompose_associativity h g f))
  | |- ⟨ ret m⊙ ?f ∈ _ |_| _ ⟩ => ReplaceBy (mcompose_left_unit f)
  | |- ⟨ ?f m⊙ ret ∈ _ |_| _ ⟩ => ReplaceBy (mcompose_right_unit f)
  end.
  
Class MonadPlus m `{! Monad m } :=
  { mzero : forall {A}, dom (m A)
  ; mplus : forall {A}, dom (m A ⇒ m A ⇒ m A)
  ; mplus_mzero_left : forall {A} (aM:dom (m A)), mplus ∙ mzero ∙ aM ≃ aM
  ; mplus_mzero_right : forall {A} (aM:dom (m A)), mplus ∙ aM ∙ mzero ≃ aM
  ; mplus_distributivity : forall {A B} (aM₁ aM₂:dom (m A)) (k:dom (A ⇒ m B)), 
      bind ∙ (mplus ∙ aM₁ ∙ aM₂) ∙ k ≃ mplus ∙ (bind ∙ aM₁ ∙ k) ∙ (bind ∙ aM₂ ∙ k)
  }.

Notation "e₁ m+ e₂" := (mplus ∙ e₁ ∙ e₂) (at level 60, right associativity).

Class MonadMorphism m₁ m₂ `{! Monad m₁ ,! Monad m₁ } :=
  { promote : forall {A}, dom (m₁ A ⇒ m₂ A) }.

Class MonadState S m `{! Monad m } :=
  { get : dom (m S)
  ; put : dom (S ⇒ m unit)
  }.