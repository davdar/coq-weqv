Require Import FP.Classes.Eqv.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.

Import Relation.Notation.

Class WeakEqv (A:Type) : Type :=
  { weqv : A -> A -> Type
  ; WeakEqv_Symmetric :> Symmetric weqv
  ; WeakEqv_Transitive :> Transitive weqv
  }.
Arguments weqv {A} {WeakEqv} _ _ : simpl never.

Definition weqv_proper_l 
  {A} `{! WeakEqv A } {x y:A} (p:weqv x y) 
  : weqv x x := transitivity y p (symmetry p).
Definition weqv_proper_r 
  {A} `{! WeakEqv A } {x y:A} (p:weqv x y) 
  : weqv y y := transitivity x (symmetry p) p.
Ltac WeqvProper :=
  match goal with
  | [ H : weqv ?x ?y |- weqv ?x ?x ] => apply (weqv_proper_l H)
  | [ H : weqv ?x ?y |- weqv ?y ?y ] => apply (weqv_proper_r H)
  end.

Instance Function_WeakEqv 
  {A B} `{! WeakEqv A ,! WeakEqv B } 
  : WeakEqv (A -> B) := { weqv := weqv ==> weqv }.
Proof.
  - constructor ; unfold "==>" ; intros f g Rfg x y Rxy.
    Symmetry.
    apply Rfg.
    Symmetry ; auto.
  - constructor ; unfold "==>" ; intros f g h Rfg Rgh x y Rxy.
    Transitivity (g x) ; [ apply Rfg | apply Rgh ] ; auto.
    WeqvProper.
Defined.

Local Instance Leibniz_WeakEqv (T:Type) : WeakEqv T := { weqv := eq }.
Proof.
  constructor ; intros ; subst ; auto.
  constructor ; intros ; subst ; auto.
Defined.
    
Module Notation.
  Infix "≈" := weqv (no associativity, at level 70).
End Notation.