Require Import FP.Core.Relations.
Require Import FP.Core.Universe.
Require Import FP.Core.QType.
Require Import FP.Core.Tactic.

Definition topk {A} : dom (A ⇒ A) := id.
Definition focusFun {A B C} (x:dom A) (k:dom (B ⇒ C)) : dom ((A ⇒ B) ⇒ C) :=
  k ⊙ applyTo ∙ x.
Definition focusArg {A B C} (f:dom (A ⇒ B)) (k:dom (B ⇒ C)) : dom (A ⇒ C) :=
  k ⊙ apply ∙ f.

Inductive mode := EQV | LTE | GTE.

Definition state {A B:qtype} (m:mode) :=
  match m with
  | EQV => fun (x:dom A) (k:dom (A ⇒ B)) (y:dom B) => k ∙ x ≃ y
  | LTE => fun (x:dom A) (k:dom (A ⇒ B)) (y:dom B) => k ∙ x ⊑ y
  | GTE => fun (x:dom A) (k:dom (A ⇒ B)) (y:dom B) => y ⊑ k ∙ x
  end.

Opaque state.

Notation "⊤κ" := topk.
Infix "◁" := focusFun (at level 60, right associativity).
Infix "▷" := focusArg (at level 60, right associativity).
Notation "⟨ x ∈ k | m | y ⟩" := (state m x k y).

Ltac EnterLeft :=
  match goal with
  | |- ?x ≃ ?y => change ⟨ x ∈ ⊤κ |EQV| y ⟩
  | |- ?x ⊑ ?y => change ⟨ x ∈ ⊤κ |LTE| y ⟩
  end.
Ltac ExitLeft :=
  match goal with
  | |- ⟨ ?x ∈ ⊤κ |EQV| ?y ⟩ => change (x ≃ y)
  | |- ⟨ ?x ∈ ⊤κ |LTE| ?y ⟩ => change (x ⊑ y)
  end.
Ltac EnterRight :=
  match goal with
  | |- ?x ≃ ?y => Symmetry ; change ⟨ y ∈ ⊤κ |EQV| x ⟩
  | |- ?x ⊑ ?y => change ⟨ y ∈ ⊤κ |GTE| x ⟩
  end.
Ltac ExitRight :=
  match goal with
  | |- ⟨ ?y ∈ ⊤κ |EQV| ?x ⟩ => change (y ≃ x) ; Symmetry
  | |- ⟨ ?y ∈ ⊤κ |GTE| ?x ⟩ => change (x ⊑ y)
  end.

Ltac PushFun :=
  match goal with
  | |- ⟨ ?f ∙ ?x ∈ ?k |EQV| ?y ⟩ => change ⟨ f ∈ (x ◁ k) |EQV| y ⟩
  | |- ⟨ ?f ∙ ?x ∈ ?k |LTE| ?y ⟩ => change ⟨ f ∈ (x ◁ k) |LTE| y ⟩
  | |- ⟨ ?f ∙ ?x ∈ ?k |GTE| ?y ⟩ => change ⟨ f ∈ (x ◁ k) |GTE| y ⟩
  end.
Ltac PopFun :=
  match goal with
  | |- ⟨ ?f ∈ (?x ◁ ?k) |EQV| ?y ⟩ => change ⟨ f ∙ x ∈ k |EQV| y ⟩
  | |- ⟨ ?f ∈ (?x ◁ ?k) |LTE| ?y ⟩ => change ⟨ f ∙ x ∈ k |LTE| y ⟩
  | |- ⟨ ?f ∈ (?x ◁ ?k) |GTE| ?y ⟩ => change ⟨ f ∙ x ∈ k |GTE| y ⟩
  end.
Ltac PushArg :=
  match goal with
  | |- ⟨ ?f ∙ ?x ∈ ?k |EQV| ?y ⟩ => change ⟨ x ∈ (f ▷ k) |EQV| y ⟩
  | |- ⟨ ?f ∙ ?x ∈ ?k |LTE| ?y ⟩ => change ⟨ x ∈ (f ▷ k) |LTE| y ⟩
  | |- ⟨ ?f ∙ ?x ∈ ?k |GTE| ?y ⟩ => change ⟨ x ∈ (f ▷ k) |GTE| y ⟩
  end.
Ltac PopArg :=
  match goal with
  | |-  ⟨ ?x ∈ (?f ▷ ?k) |EQV| ?y ⟩ => change ⟨ f ∙ x ∈ k |EQV| y ⟩
  | |-  ⟨ ?x ∈ (?f ▷ ?k) |LTE| ?y ⟩ => change ⟨ f ∙ x ∈ k |LTE| y ⟩
  | |-  ⟨ ?x ∈ (?f ▷ ?k) |GTE| ?y ⟩ => change ⟨ f ∙ x ∈ k |GTE| y ⟩
  end.

Definition eqv_replace {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B} 
(e:x ≃ x') (g:⟨ x' ∈ k |EQV| y ⟩) : ⟨ x ∈ k |EQV| y ⟩.
Proof.
  change (k ∙ x ≃ y).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition lte_replace_lte {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ⊑ x') (g:⟨ x' ∈ k |LTE| y ⟩) : ⟨ x ∈ k |LTE| y ⟩.
Proof.
  change (k ∙ x ⊑ y).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition lte_replace_eqv {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ≃ x') : ⟨ x' ∈ k |LTE| y ⟩ -> ⟨ x ∈ k |LTE| y ⟩ := lte_replace_lte (reflexivity e).
Definition gte_replace_gte {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(d:x' ⊑ x) (g:⟨ x' ∈ k |GTE| y ⟩) : ⟨ x ∈ k |GTE| y ⟩.
Proof.
  change (y ⊑ k ∙ x).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition gte_replace_eqv {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ≃ x') : ⟨ x' ∈ k |GTE| y ⟩ -> ⟨ x ∈ k |GTE| y ⟩ := 
  gte_replace_gte (reflexivity (symmetry e)).
Ltac ReplaceBy p :=
  match goal with
  | |- ⟨ ?x ∈ ?k |EQV| ?y ⟩ => apply (eqv_replace p)
  | |- ⟨ ?x ∈ ?k |LTE| ?y ⟩ => apply (lte_replace_eqv p)
  | |- ⟨ ?x ∈ ?k |GTE| ?y ⟩ => apply (gte_replace_eqv p)
  end.
Ltac WeakenBy p :=
  match goal with
  | |- ⟨ ?x ∈ ?k |LTE| ?y ⟩ => apply (lte_replace_lte p)
  end.
Ltac StrengthenBy p :=
  match goal with
  | |- ⟨ ?x ∈ ?k |GTE| ?y ⟩ => apply (gte_replace_gte p)
  end.

Ltac Everywhere_k t :=
  match goal with
  | |- ⟨ _ ∙ _ ∈ _ | _ | _ ⟩ =>
      chain PushFun ; Everywhere_k t ; PopFun |+|
      chain PushArg ; Everywhere_k t ; PopArg |+|
      t ; repeat t
  | _ => t ; repeat t
  end.
Ltac Everywhere t :=
  try (EnterLeft ; Everywhere_k t ; ExitLeft) ;
  try (EnterRight ; Everywhere_k t ; ExitRight).
Tactic Notation "Re" tactic2(t) := Everywhere t.