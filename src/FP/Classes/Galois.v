Require Import FP.Core.

Class Galois (A B:qtype) :=
  { galoisα : dom (A ⇒ B)
  ; galoisγ : dom (B ⇒ A)
  ; galois_id_αγ : galoisα ⊙ galoisγ ⊑ id
  ; galois_id_γα : id ⊑ galoisγ ⊙ galoisα
  }.
Global Opaque galoisα.
Global Opaque galoisγ.

Ltac GaloisRewrite :=
  match goal with
  | |- ⟨ (galoisα (A:=?A) (B:=?B)) ⊙ (galoisγ (A:=?A) (B:=?B)) IN _ |LTE| _ ⟩ =>
      WeakenBy (galois_id_αγ (A:=A) (B:=B))
  | |- ⟨ galoisα ∙ (galoisγ ∙ ?e) IN _ |LTE| _ ⟩ => 
      WeakenBy (qmonotonic_elim galois_id_αγ e e libReflexivity)
  | |- ⟨ (galoisγ (A:=?A) (B:=?B)) ⊙ (galoisα (A:=?A) (B:=?B)) IN _ |GTE| _ ⟩ =>
      StrengthenBy (galois_id_γα (A:=A) (B:=B))
  | |- ⟨ galoisγ ∙ (galoisα ∙ ?e) IN _ |GTE| _ ⟩ =>
      StrengthenBy (qmonotonic_elim galois_id_γα e e libReflexivity)
  end.

Instance : forall A B `{! Galois A B }, Galois (A ⇒ A) (B ⇒ B) :=
  { galoisα := λ f → galoisα ⊙ f ⊙ galoisγ
  ; galoisγ := λ g → galoisγ ⊙ g ⊙ galoisα
  }.
Proof.
  - Re fail || GaloisRewrite.
  - Re fail || GaloisRewrite.
Defined.