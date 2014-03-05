Require Import FP.Core.

Class Injection {A B} (inj:dom (A ⇒ B)) :=
  { injection : forall {x y}, inj ∙ x ≃ inj ∙ y -> x ≃ y }.
Arguments injection {A B} inj {Injection x y} _.

Ltac Injection f := apply (injection f).