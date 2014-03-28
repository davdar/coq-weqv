Require Import FP.Core.

Instance : Eqv Prop := { eqv p q := p <-> q }.
Admitted.

Instance : Lte Prop := { lte p q := p -> q }.
Admitted.

Definition prop := {| qdom := Prop |}.
Definition all {A} : dom ((A ⇒ prop) ⇒ prop) := λ f →
  (forall (x:dom A), (f ∙ x : dom prop)) : dom prop.
Definition imp : dom (prop ⇒ prop ⇒ prop) := λ p q → (p:dom prop) -> (q:dom prop) : dom prop.