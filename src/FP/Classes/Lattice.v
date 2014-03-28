Require Import FP.Core.

Class Lattice A :=
  { top : dom A
  ; bot : dom A
  ; join : dom (A ⇒ A ⇒ A)
  ; meet : dom (A ⇒ A ⇒ A)
  ; join_left : forall x y, x ⊑ join ∙ x ∙ y
  ; join_right : forall x y, y ⊑ join ∙ x ∙ y
  ; meet_left : forall x y, meet ∙ x ∙ y ⊑ x
  ; meet_right : forall x y, meet ∙ y ∙ x ⊑ y
  }.

Notation "⊤" := top.
Notation "⊥" := bot.
Notation "x ⊔ y" := (join ∙ x ∙ y).
Notation "x ⊓ y" := (meet ∙ x ∙ y).