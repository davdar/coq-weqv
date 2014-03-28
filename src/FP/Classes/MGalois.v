Require Import FP.Core.
Require Import FP.Classes.Monad.
Require Import FP.Classes.Galois.

Class MGalois m `{! Monad m } (A B:qtype) :=
  { mgaloisα : dom (A ⇒ m B)
  ; mgaloisγ : dom (B ⇒ m A)
  ; mgalois_id_αγ : mgaloisα m⊙ mgaloisγ ⊑ ret
  ; mgalois_id_γα : ret ⊑ mgaloisγ m⊙ mgaloisα
  }.
Global Opaque mgaloisα.
Global Opaque mgaloisγ.

Ltac GaloisWFRewrite :=
  match goal with
  | |- ⟨ (mgaloisα (A:=?A) (B:=?B)) m⊙ (mgaloisγ (A:=?A) (B:=?B)) IN _ |LTE| _ ⟩ =>
      WeakenBy (mgalois_id_αγ (A:=A) (B:=B))
  | |- ⟨ (mgaloisγ ∙ ?e) >>= mgaloisα IN _ |LTE| _ ⟩ => 
      WeakenBy (qmonotonic_elim mgalois_id_αγ e e libReflexivity)
  | |- ⟨ (mgaloisγ (A:=?A) (B:=?B)) m⊙ (mgaloisα (A:=?A) (B:=?B)) IN _ |GTE| _ ⟩ =>
      StrengthenBy (mgalois_id_γα (A:=A) (B:=B))
  | |- ⟨ (mgaloisα ∙ ?e) >>= mgaloisγ IN _ |GTE| _ ⟩ =>
      StrengthenBy (qmonotonic_elim mgalois_id_γα e e libReflexivity)
  end.

Section Galois1.
  Local Opaque mcompose.
  Instance : forall m A B `{! Monad m ,! MGalois m A B }, Galois (A ⇒ m A) (B ⇒ m B) :=
    { galoisα := λ f → mgaloisα m⊙ f m⊙ mgaloisγ
    ; galoisγ := λ g → mgaloisγ m⊙ g m⊙ mgaloisα
    }.
  Proof.
    Local Ltac Hammer := Re fail || MonadRewrite || GaloisWFRewrite || KleisliRewrite.
    - Hammer. 
      Re fail || KleisliUnassoc ; Hammer.
    - Hammer.
      Re fail || KleisliUnassoc ; Hammer.
  Defined.
End Galois1.


Section Galois2.
  Instance : forall m A B `{! Monad m ,! MGalois m A B }, Galois (m A) (m B) :=
    { galoisα := extend ∙ mgaloisα
    ; galoisγ := extend ∙ mgaloisγ
    }.
  Proof.
    Local Ltac Hammer := Re fail || MonadRewrite || GaloisWFRewrite.
    - Hammer.
      Transitivity (bind ∙ y ∙ ret) ; qproper_elim ; Hammer.
    - Hammer.
      Transitivity (bind ∙ x ∙ ret) ; qproper_elim ; Hammer.
  Defined.
End Galois2.