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

Inductive PFun (A B:UPO) :=
  { pfun : dom A -> dom B
  ; pfun_proper : proper (eqv ⇉ eqv) pfun
  }.
Arguments Build_PFun {A B} _ _.
Arguments pfun {A B} _ _.
Arguments pfun_proper {A B} _ _ _ _.

Local Instance PFun_Eqv (A B:UPO) : Eqv (PFun A B) :=
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

Local Instance PFun_PreOrder (A B:UPO)
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

Local Instance PArrow_PartialOrder (A B:UPO) `{! PartialOrder (dom B) }
: PartialOrder (PFun A B) := {}.
Proof.
  constructor ; intros.
  unfold "≃" ; simpl.
  unfold "⇉" ; intros.
  apply antisymmetry ; [ apply H | apply H0 ] ; auto || (apply symmetry ; auto).
Defined.

Definition PArrow_UPreOrder (A B:UPO) : UPO :=
  {| UPreOrder_dom := PFun A B |}.
Instance UPreOrder_ProperArrow : ProperArrow UPO :=
  { proper_arrow := PArrow_UPreOrder }.
Definition PArrow_UPreOrder_apply {A B:UPO} (f:dom (A ⇒ B)) (x:dom A) := pfun f x.
Definition PArrow_UPreOrder_id {A:UPO} : dom (A ⇒ A). 
refine {| pfun x := x |}.
  unfold proper,"⇉" ; auto.
Defined.
Definition PArrow_UPreOrder_compose {A B C:UPO} : dom ((B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)).
refine {| pfun := fun (g:dom (B ⇒ C)) => 
          {| pfun := fun (f:dom (A ⇒ B)) => 
             {| pfun := fun (x:dom A) => pfun g (pfun f x) |} : dom (A ⇒ C)
          |}  : dom ((A ⇒ B) ⇒ (A ⇒ C))
       |}.
Proof.
  unfold proper,"⇉" ; intros.
  unfold "≃" ; simpl.
  unfold "⇉" ; intros.
  unfold "≃" ; simpl.
  unfold "⇉" ; intros.
  apply H.
  apply H0.
  auto.
Grab Existential Variables.
  - unfold proper,"⇉" ; intros.
    unfold "≃" ; simpl.
    unfold "⇉" ; intros.
    apply (pfun_proper g).
    apply H.
    auto.
  - unfold proper,"⇉" ; intros.
    apply (pfun_proper g).
    apply (pfun_proper f).
    auto.
Defined.

Instance PArrow_UPreOrder_Arrow : Arrow PArrow_UPreOrder := 
  { lambda_p A B f := proper (eqv ⇉ eqv) f
  ; lambda A B f p := {| pfun := f ; pfun_proper := p |}
  ; apply := @PArrow_UPreOrder_apply
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

Instance PArrow_UPreOrder_Logical : Logical PArrow_UPreOrder :=
  { logical_intro A B f g p := p
  ; logical_elim A B f g p := p
  }.