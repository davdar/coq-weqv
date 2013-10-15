Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Function.
Require Import FP.Data.Relation.
Require Import FP.Classes.Eqv.

Import WeakSetoid.Notation.
Import Eqv.Notation.
Import WeakEqv.Notation.

Definition id_Q {A:WeakSetoid} : DD (A ⇨ A) := mk_DD_infer (A ⇨ A) id.

Definition id_Q_beta {A:WeakSetoid} (x:DD A) : id_Q ⊛ x ≃ x.
Proof. decide_weqv_beta. Qed.

Definition compose_Q {A B C:WeakSetoid} : DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C)) :=
  mk_DD_infer ((B ⇨ C) ⇨ (A ⇨ B) ⇨ A ⇨ C) compose.
Definition compose_Q_beta {A B C:WeakSetoid} (g:DD (B ⇨ C)) (f:DD (A ⇨ B)) (x:DD A) 
  : compose_Q ⊛ g ⊛ f ⊛ x ≃ g ⊛ (f ⊛ x).
Proof. decide_weqv_beta. Defined.

Definition apply_Q {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ A ⇨ B) :=
  mk_DD_infer ((A ⇨ B) ⇨ A ⇨ B) apply.

Definition flip_Q {A B C:WeakSetoid} : DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) :=
  mk_DD_infer ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) flip.

Definition apply_to_Q {A B:WeakSetoid} : DD (A ⇨ (A ⇨ B) ⇨ B) := flip_Q ⊛ apply_Q.