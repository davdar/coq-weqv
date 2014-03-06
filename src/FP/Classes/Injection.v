Require Import FP.Core.

Class InjectionEqv {A B} (inj:dom (A ⇒ B)) :=
  { injectionEqv : forall {x y}, inj ∙ x ≃ inj ∙ y -> x ≃ y }.
Arguments injectionEqv {A B} inj {InjectionEqv x y} _.

Class InjectionLte {A B} (inj:dom (A ⇒ B)) :=
  { injectionLte : forall {x y}, inj ∙ x ⊑ inj ∙ y -> x ⊑ y }.
Arguments injectionLte {A B} inj {InjectionLte x y} _.

Ltac Injection f := 
  match goal with
  | |- _ ≃ _ => apply (injectionEqv f)
  | |- _ ⊑ _ => apply (injectionLte f)
  end.