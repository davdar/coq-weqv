Require Import NoQ.PartialOrder.
Require Import NoQ.Monotonic.
Require Import NoQ.WeakEquivalence.
Require Import NoQ.PreOrder.
Require Import NoQ.Reflexive.
Require Import NoQ.Transitive.
Require Import NoQ.WEqv.
Require Import NoQ.Function.
Require Import NoQ.Relation.

Class GaloisConnection 
A `{! WEqv A ,! PartialOrder A }  
B `{! WEqv B ,! PartialOrder B } :=
  { galois_α : A -> B
  ; galois_α_proper : proper weqv galois_α
  ; galois_γ : B -> A
  ; galois_γ_proper : proper weqv galois_γ
  ; galois_connection : forall {x y}, proper weqv x -> proper weqv y -> (galois_α x ⊑ y <-> x ⊑ galois_γ y)
  }.

Local Ltac my_logical_weqv :=
  repeat
    (mlogical_weqv || apply galois_α_proper || apply galois_γ_proper).

Section Corollaries.
  (* These 4 corollaries are equivalent to galois_connection above *)

  Definition galois_γα_expansive 
  A `{! WEqv A ,! PartialOrder A }
  B `{! WEqv B ,! PartialOrder B }
  `{! GaloisConnection A B }
  : forall (x:A), proper weqv x -> x ⊑ galois_γ (galois_α x).
  Proof.
    intros.
    apply galois_connection ; my_logical_weqv.
    apply lte_reflexivity ; my_logical_weqv.
  Qed.

  Definition galois_αγ_contractive
  A `{! WEqv A ,! PartialOrder A }
  B `{! WEqv B ,! PartialOrder B }
  `{! GaloisConnection A B }
  : forall (y:B), proper weqv y -> galois_α (galois_γ y) ⊑ y.
  Proof.
    intros.
    apply galois_connection ; my_logical_weqv.
    apply lte_reflexivity ; my_logical_weqv.
  Qed.

  Definition galois_α_monotonic
  A `{! WEqv A ,! PartialOrder A }  
  B `{! WEqv B ,! PartialOrder B } 
  `{! GaloisConnection A B } 
  : monotonic (galois_α:A -> B).
  Proof.
    simpl ; logical_intro.
    apply galois_connection ; my_logical_weqv.
    apply (transitivity y) ; auto.
    apply galois_γα_expansive ; auto.
  Qed.

  Definition galois_γ_monotonic
  A `{! WEqv A ,! PartialOrder A }  
  B `{! WEqv B ,! PartialOrder B } 
  `{! GaloisConnection A B } 
  : monotonic (galois_γ:B -> A).
  Proof.
    simpl ; logical_intro.
    apply galois_connection ; my_logical_weqv.
    apply (transitivity x) ; auto.
    apply galois_αγ_contractive ; auto.
  Qed.
End Corollaries.

Definition Monotonic_galois_α 
{A} `{! WEqv A ,! PartialOrder A }
{B} `{! WEqv B ,! PartialOrder B }
`{! GaloisConnection A B }
(φ:A ↗ A) (p:proper weqv φ) : (B ↗ B). 
Proof.
  refine(Build_Monotonic (galois_α ∘ mfun φ ∘ galois_γ) _) ; simpl.
  destruct φ ; simpl in *.
  unfold proper,weqv in p ; simpl in *.
  logical_intro ; simpl.
  apply galois_α_monotonic ; my_logical_weqv.
  apply mfun_monotonic ; my_logical_weqv.
  apply galois_γ_monotonic ; my_logical_weqv ; auto.
Defined.

Definition Monotonic_galois_γ 
{A} `{! WEqv A ,! PartialOrder A }
{B} `{! WEqv B ,! PartialOrder B }
`{! GaloisConnection A B }
(φ:B ↗ B) (p:proper weqv φ) : (A ↗ A). 
Proof.
  refine(Build_Monotonic (galois_γ ∘ mfun φ ∘ galois_α) _) ; simpl.
  destruct φ ; simpl in *.
  unfold proper,weqv in p ; simpl in *.
  logical_intro ; simpl.
  apply galois_γ_monotonic ; my_logical_weqv.
  apply mfun_monotonic ; my_logical_weqv.
  apply galois_α_monotonic ; my_logical_weqv ; auto.
Defined.

Instance Monotonic_GaloisConnection 
{A} `{! WEqv A ,! PartialOrder A }
{B} `{! WEqv B ,! PartialOrder B }
`{! GaloisConnection A B }
: GaloisConnection (A ↗ A) (B ↗ B) :=
  { galois_α φ := Monotonic_galois_α φ galois
  ; galois_γ φ := Monotonic_galois_γ φ
  }.
Proof.
  - repeat logical_intro ; simpl.
    my_logical_weqv.
  - repeat logical_intro ; simpl.
    my_logical_weqv.
  - intros ; constructor ; intros ; simpl in *.
    + logical_intro ; simpl.
      apply (lte_change_lte (mfun x (galois_γ (galois_α x0))) (galois_γ (mfun y (galois_α y0)))).
      { destruct x,y ; simpl in *.
        apply mfun_monotonic ; my_logical_weqv.
        apply galois_γα_expansive ; my_logical_weqv.
      }
      { apply lte_reflexivity ; my_logical_weqv. }
      apply galois_connection ; my_logical_weqv.
      apply H1 ; my_logical_weqv.
    + logical_intro ; simpl.
      apply (lte_change_lte (galois_α (mfun x (galois_γ x0))) (mfun y (galois_α (galois_γ y0)))).
      { apply lte_reflexivity ; my_logical_weqv. }
      { destruct x,y ; simpl in *.
        apply mfun_monotonic0 ; my_logical_weqv.
        apply galois_αγ_contractive ; my_logical_weqv.
      }
      apply galois_connection ; my_logical_weqv.
      apply H1 ; my_logical_weqv.
Grab Existential Variables.
Defined.