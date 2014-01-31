Require Import NoQ.PreOrder.
Require Import NoQ.PartialOrder.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.
Require Import NoQ.WEqv.
Require Import NoQ.Relation.
Require Import NoQ.Antisymmetric.

Inductive Monotonic A B `{! WEqv A ,! PreOrder A ,! WEqv B ,! PreOrder B } :=
  { mfun : A -> B
  ; mfun_monotonic : monotonic mfun
  }.
Arguments Build_Monotonic {A B _ _ _ _} _ _.
Arguments mfun {A B _ _ _ _} _ _.

Infix "↗" := Monotonic (at level 90, right associativity).

Ltac mlogical_weqv := logical_weqv ||
  (repeat
    match goal with
    (* logical elimination *)
    | [ H : (weqv ↗ weqv) ?f ?g |- (mfun ?f _) ≈ (mfun ?g _) ] => apply H
    | [ H : (weqv ↗ weqv) ?f ?g |- (?g _) ≈ (?f _) ] => apply symmetry ; apply H
    | [ H : ?f ≈ ?g |- (mfun ?f _) ≈ (mfun ?g _) ] => apply H
    | [ H : ?f ≈ ?g |- (mfun ?g _) ≈ (mfun ?f _) ] => apply symmetry ; apply H
    | [ H : proper weqv ?f |- proper weqv (mfun ?f _) ] => apply H
    | [ H : proper weqv ?f |- (mfun ?f _) ≈ (mfun ?f _) ] => apply H
    end).

Instance Monotonic_WEqv {A B} `{! WEqv A ,! PreOrder A ,! WEqv B ,! PreOrder B } : WEqv (A ↗ B) :=
  { weqv f g := weqv (mfun f) (mfun g) }.
Proof.
  constructor ; constructor ; intros.
  - apply symmetry ; auto.
  - apply (transitivity (mfun y)) ; auto.
Defined.

Instance Monotonic_PreOrder {A B} `{! WEqv A ,! PreOrder A ,! WEqv B ,! PreOrder B } : PreOrder (A ↗ B) :=
  { lte f g := lte (mfun f) (mfun g) }.
Proof.
  - intros.
    apply lte_reflexivity ; auto.
  - repeat (logical_intro ; simpl ; intros).
    apply (lte_change_weqv (mfun x x1) (mfun x0 y1)).
    { apply symmetry.
      apply H.
      logical_weqv.
    }
    { apply symmetry.
      apply H0.
      logical_weqv.
    }
    apply H1 ; auto.
  - constructor ; intros.
    apply (transitivity (mfun y)) ; auto.
Defined.

Instance Monotonic_PartialOrder 
{A B} `{! WEqv A ,! PartialOrder A ,! WEqv B ,! PartialOrder B} : PartialOrder (A ↗ B) := {}.
Proof.
  constructor ; intros.
  unfold "⊑" in * ; simpl in *.
  unfold "≈" ; simpl.
  apply antisymmetry ; auto.
Defined.