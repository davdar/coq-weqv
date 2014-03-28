Require Import FP.Core.Relations.
Require Import FP.Core.Universe.
Require Import FP.Core.QType.
Require Import FP.Core.Tactic.
Require Import FP.Core.Notation.

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
Infix "◁" := focusFun.
Infix "▷" := focusArg.
Notation "⟨ x 'IN' k | m | y ⟩" := (state m x k y).

Ltac EnterLeft :=
  match goal with
  | |- ?x ≃ ?y => change ⟨ x IN ⊤κ |EQV| y ⟩
  | |- ?x ⊑ ?y => change ⟨ x IN ⊤κ |LTE| y ⟩
  end.
Ltac ExitLeft :=
  match goal with
  | |- ⟨ ?x IN ⊤κ |EQV| ?y ⟩ => change (x ≃ y)
  | |- ⟨ ?x IN ⊤κ |LTE| ?y ⟩ => change (x ⊑ y)
  end.
Ltac EnterRight :=
  match goal with
  | |- ?x ≃ ?y => Symmetry ; change ⟨ y IN ⊤κ |EQV| x ⟩
  | |- ?x ⊑ ?y => change ⟨ y IN ⊤κ |GTE| x ⟩
  end.
Ltac ExitRight :=
  match goal with
  | |- ⟨ ?y IN ⊤κ |EQV| ?x ⟩ => change (y ≃ x) ; Symmetry
  | |- ⟨ ?y IN ⊤κ |GTE| ?x ⟩ => change (x ⊑ y)
  end.

Ltac PushFun :=
  match goal with
  | |- ⟨ ?f ∙ ?x IN ?k |EQV| ?y ⟩ => change ⟨ f IN (x ◁ k) |EQV| y ⟩
  | |- ⟨ ?f ∙ ?x IN ?k |LTE| ?y ⟩ => change ⟨ f IN (x ◁ k) |LTE| y ⟩
  | |- ⟨ ?f ∙ ?x IN ?k |GTE| ?y ⟩ => change ⟨ f IN (x ◁ k) |GTE| y ⟩
  end.
Ltac PopFun :=
  match goal with
  | |- ⟨ ?f IN (?x ◁ ?k) |EQV| ?y ⟩ => change ⟨ f ∙ x IN k |EQV| y ⟩
  | |- ⟨ ?f IN (?x ◁ ?k) |LTE| ?y ⟩ => change ⟨ f ∙ x IN k |LTE| y ⟩
  | |- ⟨ ?f IN (?x ◁ ?k) |GTE| ?y ⟩ => change ⟨ f ∙ x IN k |GTE| y ⟩
  end.
Ltac PushArg :=
  match goal with
  | |- ⟨ ?f ∙ ?x IN ?k |EQV| ?y ⟩ => change ⟨ x IN (f ▷ k) |EQV| y ⟩
  | |- ⟨ ?f ∙ ?x IN ?k |LTE| ?y ⟩ => change ⟨ x IN (f ▷ k) |LTE| y ⟩
  | |- ⟨ ?f ∙ ?x IN ?k |GTE| ?y ⟩ => change ⟨ x IN (f ▷ k) |GTE| y ⟩
  end.
Ltac PopArg :=
  match goal with
  | |-  ⟨ ?x IN (?f ▷ ?k) |EQV| ?y ⟩ => change ⟨ f ∙ x IN k |EQV| y ⟩
  | |-  ⟨ ?x IN (?f ▷ ?k) |LTE| ?y ⟩ => change ⟨ f ∙ x IN k |LTE| y ⟩
  | |-  ⟨ ?x IN (?f ▷ ?k) |GTE| ?y ⟩ => change ⟨ f ∙ x IN k |GTE| y ⟩
  end.

Definition eqv_replace {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B} 
(e:x ≃ x') (g:⟨ x' IN k |EQV| y ⟩) : ⟨ x IN k |EQV| y ⟩.
Proof.
  change (k ∙ x ≃ y).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition lte_replace_lte {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ⊑ x') (g:⟨ x' IN k |LTE| y ⟩) : ⟨ x IN k |LTE| y ⟩.
Proof.
  change (k ∙ x ⊑ y).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition lte_replace_eqv {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ≃ x') : ⟨ x' IN k |LTE| y ⟩ -> ⟨ x IN k |LTE| y ⟩ := lte_replace_lte (reflexivity e).
Definition gte_replace_gte {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(d:x' ⊑ x) (g:⟨ x' IN k |GTE| y ⟩) : ⟨ x IN k |GTE| y ⟩.
Proof.
  change (y ⊑ k ∙ x).
  Transitivity (k ∙ x') ; qproper_elim.
  exact g.
Qed.
Definition gte_replace_eqv {A B} {x x':dom A} {k:dom (A ⇒ B)} {y:dom B}
(e:x ≃ x') : ⟨ x' IN k |GTE| y ⟩ -> ⟨ x IN k |GTE| y ⟩ := 
  gte_replace_gte (reflexivity (symmetry e)).
Ltac ReplaceBy p :=
  match goal with
  | |- ⟨ ?x IN ?k |EQV| ?y ⟩ => apply (eqv_replace p)
  | |- ⟨ ?x IN ?k |LTE| ?y ⟩ => apply (lte_replace_eqv p)
  | |- ⟨ ?x IN ?k |GTE| ?y ⟩ => apply (gte_replace_eqv p)
  end.
Ltac WeakenBy p :=
  match goal with
  | |- ⟨ ?x IN ?k |LTE| ?y ⟩ => apply (lte_replace_lte p)
  end.
Ltac StrengthenBy p :=
  match goal with
  | |- ⟨ ?x IN ?k |GTE| ?y ⟩ => apply (gte_replace_gte p)
  end.

Ltac Everywhere_k t :=
  chain
    (match goal with
    |- ⟨ _ ∙ _ IN _ | _ | _ ⟩ =>
        chain PushFun ; Everywhere_k t ; PopFun |+|
        PushArg ; Everywhere_k t ; PopArg
    end || fail) |+|
  (t ; repeat t).
Ltac Everywhere t :=
  try (EnterLeft ; Everywhere_k t ; ExitLeft) ;
  try (EnterRight ; Everywhere_k t ; ExitRight).
Tactic Notation "Re" tactic2(t) := repeat (Everywhere t ; qproper_elim).