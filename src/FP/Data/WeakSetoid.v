Require Import FP.Classes.WeakEqv.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Classes.Multiplicative.
Require Import FP.Data.Type.

Import Relation.Notation.
Import Function.Notation.
Import WeakEqv.Notation.
Import Multiplicative.Notation.

Inductive WeakSetoid : Type := mk_WeakSetoid
  { WeakSetoid_T : Type
  ; WeakSetoid_WeakEqv : WeakEqv WeakSetoid_T
  }.
Existing Instance WeakSetoid_WeakEqv.

Inductive DD (A:WeakSetoid) : Type := mk_DD
  { DD_value : WeakSetoid_T A
  ; DD_proper : proper weqv DD_value
  }.
Arguments mk_DD {A} _ _.
Arguments DD_value {A} _.
Arguments DD_proper {A} _.

Instance DD_WeakEqv {A:WeakSetoid} : WeakEqv (DD A) :=
  { weqv x y := (DD_value x ≈ DD_value y) }.
Proof.
  - econstructor ; intros.
    Symmetry ; auto.
  - econstructor ; intros.
    Transitivity (DD_value y) ; auto.
Defined.

Definition weak_setoid_arrow (A:WeakSetoid) (B:WeakSetoid) : WeakSetoid :=
  mk_WeakSetoid (WeakSetoid_T A -> WeakSetoid_T B) Function_WeakEqv.

Definition weak_setoid_apply {A:WeakSetoid} {B:WeakSetoid} (f:DD (weak_setoid_arrow A B)) (x:DD A) : DD B :=
  mk_DD (DD_value f $ DD_value x) (DD_proper f (DD_value x) (DD_value x) (DD_proper x)).

Module Notation.
  Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).
  Infix "⊛" := weak_setoid_apply (left associativity, at level 50).
End Notation.