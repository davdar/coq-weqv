Require Import NoQ.PartialOrder.
Require Import NoQ.Universe.
Require Import NoQ.PArrow.
Require Import NoQ.MArrow.
Require Import NoQ.PreOrder.
Require Import NoQ.Reflexive.
Require Import NoQ.LibReflexive.
Require Import NoQ.Arrow.
Require Import NoQ.Transitive.
Require Import NoQ.Eqv.
Require Import NoQ.Function.
Require Import NoQ.Relation.

Class GaloisConnection (A B:UPO) :=
  { galois_α : dom (A ⇒ B)
  ; galois_γ : dom (B ⇒ A)
  ; galois_connection : forall {x:dom A} {y:dom B}, (galois_α ∙ x) ⊑ y <-> x ⊑ (galois_γ ∙ y)
  }.

Section Corollaries.
  (* These 4 corollaries are equivalent to galois_connection above *)

  Definition galois_γα_expansive {A B} `{! GaloisConnection A B }
  : forall (x:dom A), x ⊑ galois_γ ∙ (galois_α ∙ x).
  Proof.
    intros.
    apply galois_connection.
    apply reflexivity ; logical.
  Qed.

  Definition galois_αγ_contractive {A B} `{! GaloisConnection A B }
  : forall (y:dom B), galois_α ∙ (galois_γ ∙ y) ⊑ y.
  Proof.
    intros.
    apply galois_connection.
    apply reflexivity ; logical.
  Qed.

  Definition galois_α_monotonic {A B} `{! GaloisConnection A B } 
  : proper (lte ∙⇉∙ lte) (galois_α:dom(A ⇒ B)).
  Proof.
    simpl.
    unfold proper,"∙⇉∙" ; intros.
    apply galois_connection.
    apply (transitivity y) ; auto.
    apply galois_γα_expansive ; auto.
  Qed.
  Definition mon_galois_α {A B} `{! GaloisConnection A B } : dom (A ⇗ B) :=
    {| mfun := galois_α
     ; mfun_monotonic := galois_α_monotonic
    |}.

  Definition galois_γ_monotonic {A B} `{! GaloisConnection A B } 
  : proper (lte ∙⇉∙ lte) (galois_γ:dom (B ⇒ A)).
  Proof.
    simpl.
    unfold proper,"∙⇉∙" ; intros.
    apply galois_connection.
    apply (transitivity x) ; auto.
    apply galois_αγ_contractive ; auto.
  Qed.
  Definition mon_galois_γ {A B} `{! GaloisConnection A B } : dom (B ⇗ A) :=
    {| mfun := galois_γ
     ; mfun_monotonic := galois_γ_monotonic
    |}.
  
  Definition mon_galois_connection {A B} `{! GaloisConnection A B } {x:dom A} {y:dom B}
  : (mon_galois_α ∙ x) ⊑ y <-> x ⊑ (mon_galois_γ ∙ y) := galois_connection.
  Definition mon_galois_γα_expansive {A B} `{! GaloisConnection A B }
  : forall (x:dom A), x ⊑ mon_galois_γ ∙ (mon_galois_α ∙ x) := galois_γα_expansive.
  Definition mon_galois_αγ_contractive {A B} `{! GaloisConnection A B }
  : forall (y:dom B), mon_galois_α ∙ (mon_galois_γ ∙ y) ⊑ y := galois_αγ_contractive.
End Corollaries.

Definition Monotonic_galois_α {A B} `{! GaloisConnection A B } : dom ((A ⇗ A) ⇒ (B ⇗ B)).
Proof.
  refine {| pfun φ := mon_galois_α ∙⊙∙ φ ∙⊙∙ mon_galois_γ |}.
  unfold proper,"⇉" ; intros.
  apply logical_elim ; unfold "∙⇉∙" ; intros.
  apply (eqv_change (mon_galois_α ∙ (x ∙ (mon_galois_γ ∙ x0))) 
                    (mon_galois_α ∙ (y ∙ (mon_galois_γ ∙ y0)))) ; logical.
Defined.

Definition Monotonic_galois_γ {A B} `{! GaloisConnection A B } : dom ((B ⇗ B) ⇒ (A ⇗ A)). 
  refine {| pfun φ := mon_galois_γ ∙⊙∙ φ ∙⊙∙ mon_galois_α |}.
  unfold proper,"⇉" ; intros.
  apply logical_elim ; unfold "∙⇉∙" ; intros.
  apply (eqv_change (mon_galois_γ ∙ (x ∙ (mon_galois_α ∙ x0))) 
                    (mon_galois_γ ∙ (y ∙ (mon_galois_α ∙ y0)))) ; logical.
Defined.

Instance Monotonic_GaloisConnection {A B} `{! GaloisConnection A B }
: GaloisConnection (A ⇗ A) (B ⇗ B) :=
  { galois_α := Monotonic_galois_α
  ; galois_γ := Monotonic_galois_γ
  }.
Proof.
  intros ; constructor ; intros.
  - apply monotonic_elim ; unfold "∙⇉∙" ; intros.
    change (x ∙ x0 ⊑ (mon_galois_γ ∙ (y ∙ (mon_galois_α ∙ y0)))).
    apply mon_galois_connection.
    apply (lte_change_lte
            (mon_galois_α ∙ (x ∙ (mon_galois_γ ∙ (mon_galois_α ∙ x0))))
            (y ∙ (mon_galois_α ∙ y0))) ; monotonic.
    { apply mon_galois_γα_expansive. }
    change ( (mon_galois_α ∙⊙∙ x ∙⊙∙ mon_galois_γ) ∙ (mon_galois_α ∙ x0)
           ⊑ y ∙ (mon_galois_α ∙ y0)) ; monotonic.
  - apply monotonic_elim ; unfold "∙⇉∙" ; intros.
    change (mon_galois_α ∙ (x ∙ (mon_galois_γ ∙ x0)) ⊑ y ∙ y0).
    apply mon_galois_connection.
    apply (lte_change_lte
            (x ∙ (mon_galois_γ ∙ x0))
            (mon_galois_γ ∙ (y ∙ (mon_galois_α ∙ (mon_galois_γ ∙ y0))))) ; monotonic.
    { apply mon_galois_αγ_contractive. }
    change ( (x ∙ (mon_galois_γ ∙ x0))
           ⊑ (mon_galois_γ ∙⊙∙ y ∙⊙∙ mon_galois_α) ∙ (mon_galois_γ ∙ y0)) ; monotonic.
Defined.