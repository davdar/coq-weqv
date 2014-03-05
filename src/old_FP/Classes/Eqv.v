Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Classes.WeakEqv.

Class Eqv (A:Type) : Type :=
  { eqv : A -> A -> Type
  ; Eqv_Reflexive :> Reflexive eqv
  ; Eqv_Symmetric :> Symmetric eqv
  ; Eqv_Transitive :> Transitive eqv
  }.
Arguments eqv {A} {Eqv} _ _ : simpl never.

Ltac unfold_eqv :=
  unfold eqv ;
  match goal with
  | [ |- appcontext[ (match ?X with Build_Eqv e _ _ _ => e end) ] ] => 
      let X' := eval hnf in X in 
      change X with X' ; 
      cbv iota beta
  end.

Local Instance Eqv_WeakEqv {A} `{! Eqv A } : WeakEqv A :=
  { weqv := eqv
  ; WeakEqv_Symmetric := Eqv_Symmetric
  ; WeakEqv_Transitive := Eqv_Transitive
  }.

Module Notation.
  Infix "≃" := eqv (no associativity, at level 70).
End Notation.