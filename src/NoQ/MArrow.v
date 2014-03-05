Require Import NoQ.PArrow.
Require Import NoQ.Eqv.
Require Import NoQ.PreOrder.
Require Import NoQ.Universe.
Require Import NoQ.PartialOrder.
Require Import NoQ.Relation.
Require Import NoQ.Reflexive.
Require Import NoQ.Prop.
Require Import NoQ.Equivalence.
Require Import NoQ.LibReflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Arrow.

Class MonotonicArrow U `{! Universe U } :=
  { monotonic_arrow : U -> U -> U }.
Infix "⇗" := monotonic_arrow (at level 90, right associativity).

Inductive MFun t `{! Arrow t } (A B:UPO) :=
  { mfun : dom (t A B)
  ; mfun_monotonic : proper (lte ∙⇉∙ lte) mfun
  }.
Arguments mfun {t _ A B} _.
Arguments mfun_monotonic {t _ A B} _ _ _ _.

Local Instance MFun_Eqv t `{! Arrow t } 
(A B:UPO) : Eqv (MFun t A B) :=
  { eqv f g := eqv (mfun f) (mfun g) }.
Proof.
  constructor.
  - constructor ; intros ; apply lib_reflexivity.
  - constructor ; intros ; apply symmetry ; auto.
  - constructor ; intros.
    apply (transitivity (mfun y)) ; auto.
Defined.

Local Instance MFun_PreOrder t `{! Arrow t ,! Logical t } (A B:UPO) 
: PreOrder (MFun t A B) :=
  { lte f g := lte (mfun f) (mfun g) }.
Proof.
  - unfold proper,"⇉" ; simpl ; intros.
    apply (lte_change_eqv (mfun x) (mfun x0)) ; logical.
    apply H1 ; auto.
  - constructor ; intros.
    apply reflexivity ; logical.
  - constructor ; intros.
    apply (transitivity (mfun y)).
    + apply H ; apply reflexivity ; logical.
    + apply H0 ; auto.
Defined.

Instance MArrow_PartialOrder t `{! Arrow t ,! Logical t ,! Monotonic t }
(A B:UPO) `{! PartialOrder (dom A) ,! PartialOrder (dom B) }
: PartialOrder (MFun t A B).
Proof.
  constructor ; constructor ; intros.
  apply logical_elim ; unfold "∙⇉∙" ; intros.
  apply antisymmetry ; monotonic ; apply reflexivity ; logical.
Defined.

Definition MArrow (A B:UPO) : UPO :=
  {| UPreOrder_dom := MFun proper_arrow A B |}.
Instance UPreOrder_MonotonicArrow : MonotonicArrow UPO :=
  { monotonic_arrow := MArrow }.

Definition MArrow_apply {A B:UPO} (f:dom (A ⇗ B)) (x:dom A) 
: dom B := mfun f ∙ x.
Definition MArrow_id {A:UPO} : dom (A ⇗ A).
Proof.
  refine {| mfun := id |}.
  unfold proper,"∙⇉∙" ; intros.
  apply (lte_change_eqv x y) ; try apply id_apply ; auto.
Defined.

Definition MArrow_compose 
{A B C:UPO} : dom ((B ⇗ C) ⇗ (A ⇗ B) ⇗ (A ⇗ C)).
refine {| mfun := λ (g:dom (B ⇗ C)) →
          ({| mfun := λ (f:dom (A ⇗ B)) → mfun g ∙⊙∙ mfun f |} : dom ((A ⇗ B) ⇗ (A ⇗ C)))
       |}.
Proof.
  unfold proper,"∙⇉∙" ; intros.
  apply (lte_change_eqv (mfun g ∙ (mfun f ∙ x)) (mfun g ∙ (mfun f ∙ y)))
    ; try apply compose_apply.
  apply (mfun_monotonic g).
  apply (mfun_monotonic f) ; auto.
Defined.

Instance MArrow_Arrow : Arrow MArrow :=
  { lambda_p A B f := proper (eqv ⇉ eqv) f /\ proper (lte ⇉ lte) f
  ; lambda A B f p := 
      let (peqv,plte) := p in 
      {| mfun := {| pfun := f ; pfun_proper := peqv |}
       ; mfun_monotonic := plte 
      |}
  ; id := @MArrow_id
  ; apply := @MArrow_apply
  ; compose := @MArrow_compose
  }.
Proof.
  - intros ; unfold MArrow_id,MArrow_apply ; simpl.
    apply id_apply.
  - intros ; unfold MArrow_id,MArrow_apply ; simpl.
    apply compose_apply.
  - intros ; unfold MArrow_compose ; simpl.
    change ((id ∙⊙∙ mfun f) ≃ mfun f).
    apply compose_id_left.
  - intros ; unfold MArrow_compose ; simpl.
    change ((mfun f ∙⊙∙ id) ≃ mfun f).
    apply compose_id_right.
  - intros ; unfold MArrow_compose ; simpl.
    change (((mfun h ∙⊙∙ mfun g) ∙⊙∙ mfun f) ≃ (mfun h ∙⊙∙ mfun g ∙⊙∙ mfun f)).
    apply compose_associativity.
Defined.

Instance MArrow_Logical : Logical MArrow :=
  { logical_intro A B f g p := p
  ; logical_elim A B f g p := p
  }.
Instance MArrow_Monotonic : Monotonic MArrow.
Proof.
  constructor ; intros.
  - unfold "∙⇉∙" ; intros.
    apply (lte_change_lte (f ∙ y) (g ∙ y)).
    + apply (mfun_monotonic f) ; auto.
    + apply reflexivity ; logical.
    + apply H ; logical.
  - change ((eqv ∙⇉∙ lte) f g).
    unfold "∙⇉∙" ; intros.
    apply H.
    apply reflexivity ; auto.
Defined.