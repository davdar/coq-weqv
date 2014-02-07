Require Import NoQ.Transitive.
Require Import NoQ.Relation.
Require Import NoQ.Reflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.LibReflexive.
Require Import NoQ.Eqv.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Prop.
Require Import NoQ.Universe.
Require Import NoQ.Arrow.

Class PreOrder A `{! Eqv A } :=
  { lte : relation A
  ; lte_respect_eqv : proper (eqv ⇉ eqv ⇉ implies) lte
  ; PreOrder_Reflexive :> Reflexive lte
  ; PreOrder_Transitive :> Transitive lte
  }.

Infix "⊑" := lte (at level 70, no associativity).

Definition lte_change_lte
{A} `{! Eqv A ,! PreOrder A } 
{x y:A} (x' y':A) (xRx':x ⊑ x') (yRy':y' ⊑ y) (p:x' ⊑ y') : x ⊑ y.
Proof.
  apply (transitivity x') ; auto.
  apply (transitivity y') ; auto.
Qed.

Definition lte_change_eqv
{A} `{! Eqv A ,! PreOrder A } 
{x y:A} (x' y':A) (xRx':x ≃ x') (yRy':y ≃ y') (p:x' ⊑ y') : x ⊑ y.
Proof.
  apply (lte_change_lte x' y') ; auto.
  - apply reflexivity ; auto.
  - apply reflexivity ; apply symmetry ; auto.
Qed.

Class UHasPreOrder U `{! Universe U ,! UHasEqv U } :=
  { UHasPreOrder_PreOrder :> forall (A:U), PreOrder (dom A) }.

Inductive UPreOrder :=
  { UPreOrder_dom : Type
  ; UPreOrder_Eqv : Eqv UPreOrder_dom
  ; UPreOrder_PreOrder : PreOrder UPreOrder_dom
  }.
Instance UPreOrder_Universe : Universe UPreOrder :=
  { dom := UPreOrder_dom }.
Instance UPreOrder_UHasEqv : UHasEqv UPreOrder := 
  { UHasEqv_Eqv := UPreOrder_Eqv }.
Instance UPreOrder_UHasPreOrder : UHasPreOrder UPreOrder :=
  { UHasPreOrder_PreOrder := UPreOrder_PreOrder }.

Class Monotonic {U} t `{! Universe U ,! UHasEqv U ,! UHasPreOrder U ,! Arrow U t } :=
  { monotonic_intro : 
      forall {A B:U} (f g:dom (t A B)), 
      f ⊑ g -> (lte ∙⇉∙ lte) f g
  ; monotonic_elim : 
      forall {A B:U} (f g:dom (t A B)), 
      (lte ∙⇉∙ lte) f g -> f ⊑ g 
  }.

Ltac monotonic :=
repeat
  match goal with
  | |- ?x ∙ _ ⊑ ?y ∙ _ => apply (monotonic_intro x y)
  | |- _ ⊑ _ => solve [(apply reflexivity ; apply lib_reflexivity) || auto]
  end.