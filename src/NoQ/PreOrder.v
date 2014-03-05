Require Import NoQ.Transitive.
Require Import NoQ.Relation.
Require Import NoQ.Reflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.LibReflexive.
Require Import NoQ.Eqv.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Prop.
Require Import NoQ.Universe.

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

Section Lib_PreOrder.
  Local Existing Instance Lib_Eqv.
  Local Instance Lib_PreOrder (A:Type) : PreOrder (Eqv0:=Lib_Eqv A) A := { lte := eqv }.
  Proof.
    - unfold proper,"⇉",implies ; intros.
      transitivity x ; auto.
      transitivity x0 ; auto.
    - constructor ; auto.
  Defined.
End Lib_PreOrder.

(*
Class UHasPreOrder U `{! Universe U ,! UHasEqv U } :=
  { UHasPreOrder_PreOrder :> forall (A:U), PreOrder (dom A) }.
*)

(* TODO: this will inevitably need to be a partial order *)
Inductive UPO :=
  { UPreOrder_dom : Type
  ; UPreOrder_Eqv : Eqv UPreOrder_dom
  ; UPreOrder_PreOrder : PreOrder UPreOrder_dom
  }.
Instance UPO_Universe : Universe UPO :=
  { dom := UPreOrder_dom }.
Instance UPO_Eqv : forall (A:UPO), Eqv (dom A) := UPreOrder_Eqv.
Instance UPO_PreOrder : forall (A:UPO), PreOrder (dom A) := UPreOrder_PreOrder.
(*
Instance UPreOrder_UHasEqv : UHasEqv UPreOrder := 
  { UHasEqv_Eqv := UPreOrder_Eqv }.
Instance UPreOrder_UHasPreOrder : UHasPreOrder UPreOrder :=
  { UHasPreOrder_PreOrder := UPreOrder_PreOrder }.
*)

Definition embed (A:Type) : UPO :=
  {| UPreOrder_dom := A
   ; UPreOrder_Eqv := Lib_Eqv A
   ; UPreOrder_PreOrder := Lib_PreOrder A
  |}.