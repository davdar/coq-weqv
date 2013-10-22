Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Function.
Require Import FP.Data.Relation.
Require Import FP.Classes.Eqv.
Require Import FP.Data.Function.
Require Import FP.Classes.WeakEqv.

Import WeakSetoid.Notation.
Import Eqv.Notation.
Import WeakEqv.Notation.
Import Function.Notation.

Definition id_Q {A:WeakSetoid} : DD (A ⇨ A) := λ x → x.
Definition compose_Q {A B C:WeakSetoid} : DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C)) := λ g f x → g ⊛ (f ⊛ x).
Definition apply_Q {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ A ⇨ B) := λ f x → f ⊛ x.
Definition flip_Q {A B C:WeakSetoid} : DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) := λ f y x → f ⊛ x ⊛ y.
Definition apply_to_Q {A B:WeakSetoid} : DD (A ⇨ (A ⇨ B) ⇨ B) := flip_Q ⊛ apply_Q.