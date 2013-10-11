Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Eqv.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Type.

Import Relation.Notation.
Import Function.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Inductive WeakSetoid : Type := mk_WeakSetoid
  { WeakSetoid_T : Type
  ; WeakSetoid_WeakEqv : WeakEqv WeakSetoid_T
  }.
Existing Instance WeakSetoid_WeakEqv.

Inductive DD (A:WeakSetoid) : Type := mk_DD
  { DD_value : WeakSetoid_T A
  ; DD_proper : proper weqv DD_value
  }.
Arguments DD_value {A} _.
Arguments DD_proper {A} _.

Instance DD_Eqv {A:WeakSetoid} : Eqv (DD A) :=
  { eqv x y := (DD_value x ≈ DD_value y) }.
Proof.
  - econstructor ; intros.
    apply (DD_proper x).
  - econstructor ; intros.
    Symmetry ; auto.
  - econstructor ; intros.
    Transitivity (DD_value y) ; auto.
Defined.

Definition weak_setoid_arrow (A B:WeakSetoid) : WeakSetoid :=
  mk_WeakSetoid (WeakSetoid_T A -> WeakSetoid_T B) Function_WeakEqv.
Local Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).

Definition weak_setoid_apply {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A) : DD B :=
  mk_DD B (DD_value f $ DD_value x) (DD_proper f (DD_value x) (DD_value x) (DD_proper x)).
Local Infix "⊛" := weak_setoid_apply (left associativity, at level 50).

Definition EL (A:Type) : WeakSetoid :=
  mk_WeakSetoid A (Leibniz_WeakEqv A).

Ltac decide_weqv :=
  unfold "⊛","≃" ; simpl ;
  repeat
    match goal with
    | [ |- DD_value ?x ≈ DD_value ?x ] => apply (DD_proper x)
    | [ |- DD_value ?f _ ≈ DD_value ?f _ ] => apply (DD_proper f)
    | [ q : ?x ≃ ?y |- DD_value ?x ≈ DD_value ?y ] => apply q
    | [ q : ?x ≃ ?y |- DD_value ?x _ ≈ DD_value ?y _ ] => apply q
    end ;
  auto.

Definition idQ {A:WeakSetoid} : DD (A ⇨ A) := 
  mk_DD (A ⇨ A) id (fun _ _ => id).

Definition idQ_elim {A:WeakSetoid} (x:DD A) : idQ ⊛ x ≃ x.
Proof.
  decide_weqv.
Defined.

Definition composeQ {A B C:WeakSetoid} : DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C)) :=
  mk_DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ A ⇨ C) 
        compose
        (fun _ _ Rff' g g' Rgg' x x' Rxx' => Rff' (g x) (g' x') (Rgg' x x' Rxx')).

Definition composeQ_elim 
  {A B C:WeakSetoid} (g:DD (B ⇨ C)) (f:DD (A ⇨ B)) (x:DD A) 
  : composeQ ⊛ g ⊛ f ⊛ x ≃ g ⊛ (f ⊛ x).
Proof.
  decide_weqv.
Defined.

Definition applyQ {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ A ⇨ B) :=
  mk_DD ((A ⇨ B) ⇨ A ⇨ B)
        apply
        (fun _ _ Rfg x y Rxy => Rfg x y Rxy).

Definition flipQ {A B C:WeakSetoid} : DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) :=
    mk_DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C)
          flip
          (fun _ _ Rfg y y' Ryy' x x' Rxx' => Rfg x x' Rxx' y y' Ryy').

Definition apply_toQ {A B:WeakSetoid} : DD (A ⇨ (A ⇨ B) ⇨ B) := flipQ ⊛ applyQ.

Module Notation.
  Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).
  Infix "⊛" := weak_setoid_apply (left associativity, at level 50).
End Notation.