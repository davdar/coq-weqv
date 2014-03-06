Require Import FP.Core.

Class Galois (A B:qtype) :=
  { galoisα : dom (A ⇒ B)
  ; galoisγ : dom (B ⇒ A)
  ; galois_id_αγ : (galoisα ⊙ galoisγ) ⊑ id
  ; galois_id_γα : id ⊑ (galoisγ ⊙ galoisα)
  }.
Global Opaque galoisα.
Global Opaque galoisγ.

Ltac GaloisRewrite :=
  match goal with
  | |- ⟨ (galoisα (A:=?A) (B:=?B)) ⊙ (galoisγ (A:=?A) (B:=?B)) ∈ _ |LTE| _ ⟩ =>
      WeakenBy (galois_id_αγ (A:=A) (B:=B))
  | |- ⟨ galoisα ∙ (galoisγ ∙ ?e) ∈ _ |LTE| _ ⟩ => 
      WeakenBy (qmonotonic_elim galois_id_αγ e e libReflexivity)
  | |- ⟨ (galoisγ (A:=?A) (B:=?B)) ⊙ (galoisα (A:=?A) (B:=?B)) ∈ _ |GTE| _ ⟩ =>
      StrengthenBy (galois_id_γα (A:=A) (B:=B))
  | |- ⟨ galoisγ ∙ (galoisα ∙ ?e) ∈ _ |GTE| _ ⟩ =>
      StrengthenBy (qmonotonic_elim galois_id_γα e e libReflexivity)
  end.

Instance : forall A B `{! Galois A B }, Galois (A ⇒ A) (B ⇒ B) :=
  { galoisα := λ f → galoisα ⊙ f ⊙ galoisγ
  ; galoisγ := λ g → galoisγ ⊙ g ⊙ galoisα
  }.
Proof.
  - qproper.
    Transitivity (x ∙ (galoisα ∙ (galoisγ ∙ x0))).
    + eapply (qmonotonic_elim galois_id_αγ) ; LibReflexivity.
    + qproper_elim.
      eapply (qmonotonic_elim galois_id_αγ) ; auto.
  - qproper.
    Transitivity (y ∙ (galoisγ ∙ (galoisα ∙ y0))).
    + qproper_elim.
      eapply (qmonotonic_elim galois_id_γα) ; auto.
    + eapply (qmonotonic_elim galois_id_γα) ; LibReflexivity.
Defined.