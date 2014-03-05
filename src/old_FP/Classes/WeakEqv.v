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
Local Infix "≈" := weqv (no associativity, at level 70).

Ltac unfold_weqv :=
  unfold weqv ;
  match goal with
  | [ |- appcontext[ (match ?X with Build_WeakEqv e _ _ => e end) ] ] => 
      let X' := eval hnf in X in 
      change X with X' ; 
      cbv iota beta
  end.

Section proper.
  Context {A} `{! WeakEqv A } {x y:A} (p:x ≈ y).
  Definition weqv_proper_l : x ≈ x := transitivity y p (symmetry p).
  Definition weqv_proper_r : y ≈ y := transitivity x (symmetry p) p.
End proper.

Ltac WeqvProper :=
  match goal with
  | [ H : ?x ≈ ?y |- ?x ≈ ?x ] => apply (weqv_proper_l H)
  | [ H : ?x ≈ ?y |- ?y ≈ ?y ] => apply (weqv_proper_r H)
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

Section Function.
  Context {A B} `{! WeakEqv A ,! WeakEqv B}.

  (* Respect introduction for _->_ *)
  Definition fun_respect_intro
    (f g:A -> B) (p:forall x y, x ≈ y -> f x ≈ g y)
    : f ≈ g := p.

  (* Respect elimination for _->_ *)
  Definition fun_respect_elim
    (f g:A -> B) (pf:f ≈ g) (x y:A) (px:x ≈ y)
    : f x ≈ g y := pf x y px.
End Function.

Local Instance Leibniz_WeakEqv (T:Type) : WeakEqv T := { weqv := eq }.
Proof.
  - constructor ; intros ; subst ; auto.
  - constructor ; intros ; subst ; auto.
Defined.
    
Module Notation.
  Infix "≈" := weqv (no associativity, at level 70).
End Notation.