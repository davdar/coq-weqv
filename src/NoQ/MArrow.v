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

Inductive MFun {U} t `{! Universe U ,! UHasEqv U ,! UHasPreOrder U ,! Arrow U t } (A B:U) :=
  { mfun : dom (t A B)
  ; mfun_monotonic : proper (lte ∙⇉∙ lte) mfun
  }.
Arguments mfun {U t _ _ _ _ A B} _.
Arguments mfun_monotonic {U t _ _ _ _ A B} _ _ _ _.

Local Instance MFun_Eqv 
U t `{! Universe U ,! UHasEqv U ,! UHasPreOrder U ,! Arrow U t } 
(A B:U) : Eqv (MFun t A B) :=
  { eqv f g := eqv (mfun f) (mfun g) }.
Proof.
  constructor.
  - constructor ; intros ; apply lib_reflexivity.
  - constructor ; intros ; apply symmetry ; auto.
  - constructor ; intros.
    apply (transitivity (mfun y)) ; auto.
Defined.

Local Instance MFun_PreOrder 
U t `{! Universe U ,! UHasEqv U ,! UHasPreOrder U ,! Arrow U t ,! Logical t }
(A B:U) : PreOrder (MFun t A B) :=
  { lte f g := (lte ∙⇉∙ lte) (mfun f) (mfun g) }.
Proof.
  - unfold proper,"⇉" ; simpl ; intros.
    unfold "∙⇉∙" ; intros.
    (* THIS FAILS MISERABLY WHEN SET UP SPECIFICALLY TO UPreOrder, because:
       UPreOrder_Eqv fails to unify with UHasEqv_Eqv
       Grrrrrrr
    *)
    apply (lte_change_eqv (mfun x ∙ x1) (mfun x0 ∙ y1)) ; logical.
    apply H1 ; auto.
  - constructor ; intros.
    unfold "∙⇉∙" ; intros.
    apply (lte_change_eqv (mfun y ∙ x0) (mfun y ∙ y0)) ; logical.
    apply (mfun_monotonic y) ; auto.
  - constructor ; intros.
    unfold "∙⇉∙" ; intros.
    apply (transitivity (mfun y ∙ x0)).
    + apply H ; apply reflexivity ; logical.
    + apply H0 ; auto.
Defined.

Instance MArrow_PartialOrder
U t `{! Universe U ,! UHasEqv U ,! UHasPreOrder U ,! Arrow U t ,! Logical t ,! Monotonic t }
(A B:U) `{! PartialOrder (dom A) ,! PartialOrder (dom B) }
: PartialOrder (MFun t A B).
Proof.
  constructor ; constructor ; intros.
  apply logical_elim ; unfold "∙⇉∙" ; intros.
  apply antisymmetry ; monotonic. 
  - apply monotonic_elim ; unfold "∙⇉∙" ; intros.
    apply H ; auto.
  - apply reflexivity ; logical.
  - apply monotonic_elim ; unfold "∙⇉∙" ; intros.
    apply H0 ; auto.
  - apply reflexivity ; logical.
Defined.

Definition MArrow (A B:UPreOrder) : UPreOrder :=
  {| UPreOrder_dom := MFun proper_arrow A B |}.
Instance UPreOrder_MonotonicArrow : MonotonicArrow UPreOrder :=
  { monotonic_arrow := MArrow }.
(* HERE *)

Definition MArrow_apply {A B:UPreOrder} (f:dom (A ⇗ B)) (x:dom A) 
: dom B := mfun f ∙ x.
Definition MArrow_id {A:UPreOrder} : dom (A ⇗ A).
Proof.
  refine {| mfun := id |}.
  unfold proper,"∙⇉∙" ; intros.
  apply (lte_change_eqv x y) ; try apply id_apply ; auto.
Defined.

Definition MArrow_compose 
{A B C:UPreOrder} (g:dom (B ⇗ C)) (f:dom (A ⇗ B)) 
: dom (A ⇗ C).
Proof.
  refine {| mfun := mfun g ∙⊙∙ mfun f |}.
  unfold proper,"∙⇉∙" ; intros.
  apply (lte_change_eqv (mfun g ∙ (mfun f ∙ x)) (mfun g ∙ (mfun f ∙ y)))
    ; try apply compose_apply.
  apply (mfun_monotonic g).
  apply (mfun_monotonic f) ; auto.
Defined.

Instance MArrow_Arrow : Arrow UPreOrder MArrow :=
  { id := @MArrow_id
  ; apply := @MArrow_apply
  ; compose := @MArrow_compose
  }.
Proof.
  - intros ; unfold MArrow_id,MArrow_apply ; simpl.
    change UPreOrder_Eqv with UHasEqv_Eqv.
    apply id_apply.
  - intros ; unfold MArrow_id,MArrow_apply ; simpl.
    change UPreOrder_Eqv with UHasEqv_Eqv.
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
Instance MArrow_Monotonic : Monotonic MArrow :=
  { monotonic_intro A B f g p := p
  ; monotonic_elim A B f g p := p
  }.