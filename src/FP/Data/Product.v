Require Import FP.Core.

Infix "v×" := (prod : Type -> Type -> Type) (at level 70, right
associativity).

Inductive prod_eqv {A B} `{! Eqv A ,! Eqv B } : relation (A v× B) :=
  | ProdEqv : forall xl xr yl yr, xl ≃ yl -> xr ≃ yr -> prod_eqv (xl, xr) (yl, yr).
Inductive prod_lte {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } : relation (A v× B) :=
  | ProdLte : forall xl xr yl yr, xl ⊑ yl -> xr ⊑ yr -> prod_lte (xl, xr) (yl, yr).
Instance : forall A B `{! Eqv A ,! Eqv B }, Eqv (A v× B) := { eqv := prod_eqv }.
Admitted.
Instance : forall A B `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B }, Lte (A v× B) := { lte := prod_lte }.
Admitted.

Definition qprod (A B:qtype) : qtype := {| qdom := dom A v× dom B |}.
Infix "×" := qprod (at level 80, right associativity).
Definition pair {A B} : dom (A ⇒ B ⇒ (A × B)) := λ a b → ((a, b) : dom (A × B)).
Notation "x ,, y" := (pair ∙ x ∙ y) (at level 190, right associativity).
Definition prod_elim {A B C} : dom ((A × B) ⇒ (A ⇒ B ⇒ C) ⇒ C) :=
  λ ab f → match ab : dom (A × B) with (a,b) => f ∙ a ∙ b end.
Definition first {A B} : dom ((A × B) ⇒ A) := λ ab → prod_elim ∙ ab ∙ (λ a _ → a).
Definition second {A B} : dom ((A × B) ⇒ B) := λ ab → prod_elim ∙ ab ∙ (λ _ b → b).
Definition prod_beta {A B C} (p:dom (A × B)) (f:dom (A ⇒ B ⇒ C)) 
: prod_elim ∙ p ∙ f ≃ f ∙ (first ∙ p) ∙ (second ∙ p).
Proof.
  destruct p ; simpl ; qproper_elim.
Qed.
Definition prod_eta {A B} (p:dom (A × B)) : (first ∙ p ,, second ∙ p) ≃ p.
Proof.
  destruct p ; simpl ; qproper_elim.
Qed.
Definition prod_first {A B} (a:dom A) (b:dom B) : first ∙ (a ,, b) ≃ a := libReflexivity a.
Definition prod_second {A B} (a:dom A) (b:dom B) : second ∙ (a ,, b) ≃ b := libReflexivity b.
Global Opaque pair.
Global Opaque prod_elim.
Global Opaque first.
Global Opaque second.

Ltac ProdRewrite :=
  match goal with
  | |- ⟨ prod_elim ∙ ?p ∙ ?f ∈ _ ⋈ _ ⟩ => ReplaceBy (prod_beta p f)
  | |- ⟨ first ∙ ?p ,, second ∙ ?p ∈ _ ⋈ _ ⟩ => ReplaceBy (prod_eta p)
  | |- ⟨ first ∙ (?a ,, ?b) ∈ _ ⋈ _ ⟩ => ReplaceBy (prod_first a b)
  | |- ⟨ second ∙ (?a ,, ?b) ∈ _ ⋈ _ ⟩ => ReplaceBy (prod_second a b)
  end.

Definition prod_elim3 {A B C D} : dom ((A × B × C) ⇒ (A ⇒ B ⇒ C ⇒ D) ⇒ D) :=
  λ abc f → prod_elim ∙ abc $ λ a bc → prod_elim ∙ bc $ λ b c → f ∙ a ∙ b ∙ c.
Definition prod_elim4 {A B C D E} : dom ((A × B × C × D) ⇒ (A ⇒ B ⇒ C ⇒ D ⇒ E) ⇒ E) :=
  λ abcd f → prod_elim3 ∙ abcd $ λ a b cd → prod_elim ∙ cd $ λ c d → f ∙ a ∙ b ∙ c ∙ d.
Definition uncurry {A B C} : dom ((A ⇒ B ⇒ C) ⇒ ((A × B) ⇒ C)) :=
  λ f ab → prod_elim ∙ ab ∙ f.