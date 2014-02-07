Require Import NoQ.ProperFunction.
Require Import NoQ.PreOrder.
Require Import NoQ.Function.
Require Import NoQ.LibReflexive.
Require Import NoQ.Reflexive.
Require Import NoQ.PartialOrder.
Require Import NoQ.Symmetric.
Require Import NoQ.Logical.
Require Import NoQ.Transitive.
Require Import NoQ.Eqv.
Require Import NoQ.Relation.
Require Import NoQ.Antisymmetric.

Inductive MonotonicFunction A B 
`{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B } :=
  { mfun : A ⇒ B
  ; mfun_monotonic : monotonic mfun
  }.
Arguments Build_MonotonicFunction {A B _ _ _ _} _ _.
Arguments mfun {A B _ _ _ _} _.
Infix "⇗" := MonotonicFunction (at level 90, right associativity).

Instance MonotonicFunction_Apply
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B }
: Apply A B (A ⇗ B) :=
  { apply f x := mfun f ⊙ x }.

Instance MonotonicFunction_Eqv 
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B } 
: Eqv (A ⇗ B) :=
  { eqv f g := ((eqv:relation A) ⊙⇉ (eqv:relation B)) f g }.
Proof.
  constructor ; constructor ; intros.
  - unfold "⊙⇉" ; intros.
    unfold "⊙" ; unfold MonotonicFunction_Apply.
    apply logical_intro ; auto.
    apply lib_reflexivity.
  - unfold "⊙⇉" ; intros.
    unfold "⊙" ; unfold MonotonicFunction_Apply.
    apply logical_intro ; auto.
    apply symmetry ; auto.
  - unfold "⊙⇉" ; intros.
    unfold "⊙" ; unfold MonotonicFunction_Apply.
    apply logical_intro ; auto.
    apply (transitivity (mfun y)) ; auto.
Defined.

Instance MonotonicFunction_Logical 
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B }
: Logical A B (A ⇗ B) :=
  { logical_intro x y p := p
  ; logical_elim x y p := p
  }.

Definition mintro
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B }
: forall (f g:A ⇗ B), f ≃ g ->
  forall (x y:A), x ≃ y ->
  f ⊙ x ≃ g ⊙ y := logical_intro.
  
Definition melim 
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B }
: forall (f g:A ⇗ B),
  (forall (x y:A), x ≃ y -> f ⊙ x ≃ g ⊙ y) -> 
  f ≃ g := logical_elim.

Ltac mlogical0 :=
  match goal with
  | [ |- _ ⊙ _ ≃ _ ⊙ _ ] => apply mintro
  | [ |- _ ≃ _ ] => apply lib_reflexivity
  | [ |- _ ≃ _ ] => apply symmetry ; solve [ auto ]
  end.

Ltac mlogical := repeat mlogical0.

Instance MonotonicFunction_PreOrder 
{A B} `{! Eqv A ,! PreOrder A ,! Eqv B ,! PreOrder B } 
: PreOrder (A ⇗ B) := 
  { lte f g := lte (mfun f) (mfun g) }.
Proof.
  - unfold proper,"⇉" ; simpl ; intros.
    unfold "⊙⇉" ; intros.
    apply (lte_change_eqv (mfun x ⊙ x1) (mfun x0 ⊙ y1)) ; mlogical.
    apply H1 ; auto.
  - constructor ; intros.
    apply reflexivity ; auto.
  - constructor ; intros.
    apply (transitivity (mfun y)) ; auto.
Defined.

Instance Monotonic_PartialOrder 
{A B} `{! Eqv A ,! PartialOrder A ,! Eqv B ,! PartialOrder B} 
: PartialOrder (A ⇗ B) := {}.
Proof.
  constructor ; intros.
  apply melim ; intros.
  apply antisymmetry.
  apply H ; auto.
  apply H0 ; apply symmetry ; auto.
Defined.