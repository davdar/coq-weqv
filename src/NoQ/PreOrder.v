Require Import NoQ.Transitive.
Require Import NoQ.Relation.
Require Import NoQ.Symmetric.
Require Import NoQ.WEqv.
Require Import NoQ.Antisymmetric.
Require Import NoQ.Prop.
Require Import NoQ.WeakEquivalence.

Class PreOrder A `{! WEqv A } :=
  { lte : relation A
  ; lte_reflexivity : forall {x y}, x ≈ y -> lte x y
  ; lte_respect : proper (weqv ⇉ weqv ⇉ implies) lte
  ; PreOrder_Transitive :> Transitive lte
  }.

Infix "⊑" := lte (at level 70, no associativity).

Definition lte_change_lte
{A} `{! WEqv A ,! PreOrder A } 
{x y:A} (x' y':A) (xRx':x ⊑ x') (yRy':y' ⊑ y) (p:x' ⊑ y') : x ⊑ y.
Proof.
  apply (transitivity x') ; auto.
  apply (transitivity y') ; auto.
Qed.

Definition lte_change_weqv
{A} `{! WEqv A ,! PreOrder A } 
{x y:A} (x' y':A) (xRx':x ≈ x') (yRy':y ≈ y') (p:x' ⊑ y') : x ⊑ y.
Proof.
  apply (lte_change_lte x' y') ; auto.
  - apply lte_reflexivity ; auto.
  - apply lte_reflexivity ; apply symmetry ; auto.
Qed.

Definition monotonic 
{A} `{! WEqv A ,! PreOrder A }
{B} `{! WEqv B ,! PreOrder B }
(f:A -> B) := proper (weak_respectful lte lte) f.
Arguments monotonic {A _ _ B _ _} f /.
          
Instance Function_PreOrder 
{A} `{! WEqv A ,! PreOrder A }
{B} `{! WEqv B ,! PreOrder B }
: PreOrder (A -> B) :=
  { lte := respectful weqv lte }.
Proof.
  - intros.
    logical_intro.
    apply lte_reflexivity ; logical_weqv.
  - repeat (logical_intro ; simpl ; intros).
    apply (lte_change_weqv (x x1) (x0 y1)) ; logical_weqv.
    apply H1 ; logical_weqv.
  - constructor ; intros ; logical_intro.
    apply (transitivity (y y0)).
    + apply H ; logical_weqv.
    + apply H0 ; logical_weqv.
Defined.