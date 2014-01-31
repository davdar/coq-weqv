Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.
Require Import NoQ.Relation.

Class WeakEquivalence {A} (R:relation A) :=
  { WeakEquivalence_Symmetric :> Symmetric R
  ; WeakEquivalence_Transitive :> Transitive R
  }.

Definition proper_left 
{A} {R:relation A} `{! WeakEquivalence R } 
: forall {x y}, R x y -> R x x.
Proof.
  intros.
  apply (transitivity y) ; auto.
  apply symmetry ; auto.
Qed.

Definition proper_right
{A} {R:relation A} `{! WeakEquivalence R } 
: forall {x y}, R x y -> R y y.
Proof.
  intros.
  apply (transitivity x) ; auto.
  apply symmetry ; auto.
Qed.
