Require Import FP.Core.Relations.
Require Import FP.Core.Universe.
Require Import FP.Core.QType.
Require Import FP.Core.Tactic.

Definition topk {A} : dom (A ⇒ A) := id.
Definition focusFun {A B C} (x:dom A) (k:dom (B ⇒ C)) : dom ((A ⇒ B) ⇒ C) :=
  k ⊙ applyTo ∙ x.
Definition focusArg {A B C} (f:dom (A ⇒ B)) (k:dom (B ⇒ C)) : dom (A ⇒ C) :=
  k ⊙ apply ∙ f.

Definition state {A B:qtype} (x:dom A) (k:dom (A ⇒ B)) (y:dom B) := 
  k ∙ x ≃ y.
Opaque state.

Notation "⊤κ" := topk.
Infix "◁" := focusFun (at level 60, right associativity).
Infix "▷" := focusArg (at level 60, right associativity).
Notation "⟨ x ∈ k ⋈ y ⟩" := (state x k y).

Ltac Enter :=
  match goal with
  |- ?x ≃ ?y => change ⟨ x ∈ ⊤κ ⋈ y ⟩
  end.
Ltac Exit :=
  match goal with
  |- ⟨ ?x ∈ ⊤κ ⋈ ?y ⟩ => change (x ≃ y)
  end.
Ltac PushFun :=
  match goal with
  |- ⟨ ?f ∙ ?x ∈ ?k ⋈ ?y ⟩ => change ⟨ f ∈ (x ◁ k) ⋈ y ⟩
  end.
Ltac PopFun :=
  match goal with
  |- ⟨ ?f ∈ (?x ◁ ?k) ⋈ ?y ⟩ => change ⟨ f ∙ x ∈ k ⋈ y ⟩
  end.
Ltac PushArg :=
  match goal with
  |- ⟨ ?f ∙ ?x ∈ ?k ⋈ ?y ⟩ => change ⟨ x ∈ (f ▷ k) ⋈ y ⟩
  end.
Ltac PopArg :=
  match goal with
  |-  ⟨ ?x ∈ (?f ▷ ?k) ⋈ ?y ⟩ => change ⟨ f ∙ x ∈ k ⋈ y ⟩
  end.

Definition replace {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B} 
(e:x ≃ x') (g:⟨ x' ∈ k ⋈ y ⟩) : ⟨ x ∈ k ⋈ y ⟩.
Proof.
  change (k ∙ x ≃ y).
  Transitivity (k ∙ x').
  - qproper_elim.
  - exact g.
Qed.
Ltac ReplaceBy p :=
  match goal with
  |- ⟨ ?x ∈ ?k ⋈ ?y ⟩ => apply (replace p)
  end.

Ltac Everywhere_k t :=
  match goal with
  | |- ⟨ _ ∙ _ ∈ _ ⋈ _ ⟩ =>
      chain PushFun ; Everywhere_k t ; PopFun |+|
      chain PushArg ; Everywhere_k t ; PopArg |+|
      t ; repeat t
  | _ => t ; repeat t
  end.
Ltac Everywhere_1 t := Enter ; Everywhere_k t ; Exit.
Ltac Everywhere t :=
  try Everywhere_1 t ;
  try (Symmetry ; Everywhere_1 t ; Symmetry).
Tactic Notation "Re" tactic2(t) := Everywhere t.