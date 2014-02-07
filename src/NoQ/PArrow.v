Require Import NoQ.Eqv.
Require Import NoQ.Universe.
Require Import NoQ.Relation.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.
Require Import NoQ.Equivalence.
Require Import NoQ.Reflexive.
Require Import NoQ.LibReflexive.
Require Import NoQ.Antisymmetric.
Require Import NoQ.PartialOrder.
Require Import NoQ.PreOrder.
Require Import NoQ.Universe.
Require Import NoQ.Arrow.

Class ProperArrow U `{! Universe U } :=
  { proper_arrow : U -> U -> U }.
Infix "⇒" := proper_arrow (at level 90, right associativity).

Inductive PFun {U} `{! Universe U ,! UHasEqv U } (A B:U) :=
  { pfun : dom A -> dom B
  ; pfun_proper : proper (eqv ⇉ eqv) pfun
  }.
Arguments Build_PFun {_ _ _ A B} _ _.
Arguments pfun {_ _ _ A B} _ _.
Arguments pfun_proper {_ _ _ A B} _ _ _ _.

Local Instance PFun_Eqv 
{U} `{! Universe U ,! UHasEqv U } (A B:U) 
: Eqv (PFun A B) :=
  { eqv f g := (eqv ⇉ eqv) (pfun f) (pfun g) }.
Proof.
  constructor ; constructor ; intros ; unfold "⇉" ; intros.
  - apply (pfun_proper x) ; auto.
  - apply symmetry.
    apply H.
    apply symmetry ; auto.
  - apply (transitivity (pfun y x0)).
    + apply H ; apply lib_reflexivity.
    + apply H0 ; auto.
Defined.

(* This definition relies of Arrow and Logical, and is thus useless for defining arr its self *)
Section Logical_PreOrder.
  Local Instance Logical_PreOrder 
  {U arr} `{! Universe U ,! UHasEqv U ,! Arrow U arr ,! Logical arr }
  (A B:U) `{! PreOrder (dom B) }
  : PreOrder (dom (arr A B)) := { lte := (eqv ∙⇉∙ lte) }.
  Proof.
    - unfold proper,"⇉" ; simpl ; intros.
      unfold "∙⇉∙" ; intros.
      apply (lte_change_eqv (x ∙ x1) (x0 ∙ y1)) ; logical.
      apply H1 ; auto.
    - constructor ; unfold "∙⇉∙" ; intros.
      apply reflexivity ; logical ; auto.
    - constructor ; unfold "∙⇉∙" ; intros.
      apply (transitivity (y ∙ x0)) ; [ apply H | apply H0 ] ; logical ; auto.
  Defined.
End Logical_PreOrder.

Local Instance PFun_PreOrder
{U} `{! Universe U ,! UHasEqv U } 
(A B:U) `{! PreOrder (dom B) }
: PreOrder (PFun A B) :=
  { lte f g := (eqv ⇉ lte) (pfun f) (pfun g) }.
Proof.
  - unfold proper,"⇉" ; simpl ; intros.
    apply (lte_change_eqv (pfun x x1) (pfun x0 y1)).
    { apply symmetry ; apply H ; apply lib_reflexivity. }
    { apply symmetry ; apply H0 ; apply lib_reflexivity. }
    apply H1 ; auto.
  - constructor ; unfold "⇉" ; intros.
    apply reflexivity.
    apply H ; auto.
  - constructor ; unfold "⇉" ; intros.
    apply (transitivity (pfun y x0)).
    + apply H ; apply lib_reflexivity.
    + apply H0 ; auto.
Defined.

Local Instance PArrow_PartialOrder
{U} `{! Universe U ,! UHasEqv U }
(A B:U) `{! PreOrder (dom B) ,! PartialOrder (dom B) }
: PartialOrder (PFun A B) := {}.
Proof.
  constructor ; intros.
  unfold "≃" ; simpl.
  unfold "⇉" ; intros.
  apply antisymmetry ; [ apply H | apply H0 ] ; auto || (apply symmetry ; auto).
Defined.

Section ___PArrow_For_UEqv_Universe___.

  Definition PArrow_UEqv (A B:UEqv) : UEqv := 
    {| UEqv_dom := PFun A B |}.
  Global Instance UEqv_ProperArrow : ProperArrow UEqv :=
    { proper_arrow := PArrow_UEqv }.
  Definition PArrow_UEqv_apply {A B:UEqv} (f:dom (A ⇒ B)) (x:dom A) := pfun f x.
  Definition PArrow_UEqv_id {A:UEqv} : dom (A ⇒ A). 
    refine {| pfun x := x |}.
    unfold proper,"⇉" ; auto.
  Defined.
  Definition PArrow_UEqv_compose {A B C:UEqv} (g:dom (B ⇒ C)) (f:dom (A ⇒ B)) : dom (A ⇒ C).
    refine {| pfun x := pfun g (pfun f x) |}.
    unfold proper,"⇉" ; intros.
    apply (pfun_proper g).
    apply (pfun_proper f) ; auto.
  Defined.

  Global Instance PArrow_UEqv_Arrow : Arrow UEqv PArrow_UEqv := 
    { apply := @PArrow_UEqv_apply
    ; id := @PArrow_UEqv_id
    ; compose := @PArrow_UEqv_compose
    }.
  Proof.
    - intros ; apply lib_reflexivity.
    - intros ; apply lib_reflexivity.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper f) ; auto.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper f) ; auto.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper h).
      apply (pfun_proper g).
      apply (pfun_proper f) ; auto.
  Defined.

  Global Instance PArrow_Logical : Logical PArrow_UEqv :=
    { logical_intro A B f g p := p
    ; logical_elim A B f g p := p
    }.

End ___PArrow_For_UEqv_Universe___.

Section ___PArrow_For_UPreOrder_Universe___.

  Definition PArrow_UPreOrder (A B:UPreOrder) : UPreOrder :=
    {| UPreOrder_dom := PFun A B |}.
  Global Instance UPreOrder_ProperArrow : ProperArrow UPreOrder :=
    { proper_arrow := PArrow_UPreOrder }.
  Definition PArrow_UPreOrder_apply {A B:UPreOrder} (f:dom (A ⇒ B)) (x:dom A) := pfun f x.
  Definition PArrow_UPreOrder_id {A:UPreOrder} : dom (A ⇒ A). 
    refine {| pfun x := x |}.
    unfold proper,"⇉" ; auto.
  Defined.
  Definition PArrow_UPreOrder_compose {A B C:UPreOrder} (g:dom (B ⇒ C)) (f:dom (A ⇒ B)) : dom (A ⇒ C).
    refine {| pfun x := pfun g (pfun f x) |}.
    unfold proper,"⇉" ; intros.
    apply (pfun_proper g).
    apply (pfun_proper f) ; auto.
  Defined.

  Global Instance PArrow_UPreOrder_Arrow : Arrow UPreOrder PArrow_UPreOrder := 
    { apply := @PArrow_UPreOrder_apply
    ; id := @PArrow_UPreOrder_id
    ; compose := @PArrow_UPreOrder_compose
    }.
  Proof.
    - intros ; apply lib_reflexivity.
    - intros ; apply lib_reflexivity.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper f) ; auto.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper f) ; auto.
    - intros ; simpl.
      unfold "≃" ; simpl.
      unfold "⇉" ; intros.
      apply (pfun_proper h).
      apply (pfun_proper g).
      apply (pfun_proper f) ; auto.
  Defined.

  Global Instance PArrow_UPreOrder_Logical : Logical PArrow_UPreOrder :=
    { logical_intro A B f g p := p
    ; logical_elim A B f g p := p
    }.

End ___PArrow_For_UPreOrder_Universe___.