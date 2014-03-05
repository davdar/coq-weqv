Require Import FP.Core.

Class Galois (A B:qtype) :=
  { galoisβ : dom (A ⇒ B)
  ; galoisα : dom (B ⇒ A)
  ; galois_idL : (galoisβ ⊙ galoisα) ⊑ id
  ; galois_idR : id ⊑ (galoisα ⊙ galoisβ)
  }.

Instance : forall A B `{! Galois A B }, Galois (A ⇒ A) (B ⇒ B) :=
  { galoisβ := λ f → galoisβ ⊙ f ⊙ galoisα
  ; galoisα := λ g → galoisα ⊙ g ⊙ galoisβ
  }.
Proof.
  - qproper.
    Transitivity (x ∙ (galoisβ ∙ (galoisα ∙ x0))).
    + eapply (qmonotonic_elim galois_idL) ; LibReflexivity.
    + qproper_elim.
      eapply (qmonotonic_elim galois_idL) ; auto.
  - qproper.
    Transitivity (y ∙ (galoisα ∙ (galoisβ ∙ y0))).
    + qproper_elim.
      eapply (qmonotonic_elim galois_idR) ; auto.
    + eapply (qmonotonic_elim galois_idR) ; LibReflexivity.
Defined.