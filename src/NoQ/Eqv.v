Require Import NoQ.Equivalence.
Require Import NoQ.Transitive.
Require Import NoQ.Universe.

Class Eqv A :=
  { eqv : A -> A -> Prop
  ; Eqv_Equivalence :> Equivalence eqv
  }.
Arguments Build_Eqv {A} _ _.
Arguments eqv {A _} _ _ : simpl never.
Infix "≃" := eqv (at level 70, no associativity).

Definition eqv_change
{A} `{! Eqv A }
{x y:A} (x' y':A) (xRx':x ≃ x') (yRy':y' ≃ y) (p:x' ≃ y') : x ≃ y.
Proof.
  apply (transitivity x') ; auto.
  apply (transitivity y') ; auto.
Qed.

Class UHasEqv U `{! Universe U } :=
  { UHasEqv_Eqv :> forall (A:U), Eqv (dom A) }.

Inductive UEqv :=
  { UEqv_dom : Type
  ; UEqv_Eqv : Eqv UEqv_dom
  }.
Instance UEqv_Universe : Universe UEqv :=
  { dom := UEqv_dom }.
Instance UEqv_UHasEqv : UHasEqv UEqv :=
  { UHasEqv_Eqv := UEqv_Eqv }.
Hint Unfold UEqv_UHasEqv : typeclass_instances.

Definition Lib_Eqv (A:Type) : Eqv A.
Proof.
  refine {| eqv := eq |}.
  constructor ; constructor ; intros ; auto.
  transitivity y ; auto.
Defined.