Require Import FP.Core.Relations.
Require Import FP.Core.Universe.
Require Import FP.Core.RFunction.

Inductive qtype : Type := QType
  { qdom : Type
  ; qEqv : Eqv qdom
  ; qLte : Lte qdom
  }.
Instance : Universe qtype := { dom := qdom }.
Instance : forall (τ:qtype), Eqv (dom τ) := qEqv.
Instance : forall (τ:qtype), Lte (dom τ) := qLte.
Global Opaque Eqv_instance_0.
Global Opaque Lte_instance_0.

Definition lib (A:Type) : qtype :=
  {| qdom := A
   ; qEqv := lib_Eqv
   ; qLte := trivial_Lte
  |}.

Definition dual (τ:qtype) : qtype :=
  {| qdom := dom τ
   ; qEqv := qEqv τ
   ; qLte := dualLte
  |}.

Definition flip_intro {τ} {x y:dom τ} (p:x ⊑ y) : (y:dom (dual τ)) ⊑ (x:dom (dual τ)) := p.
Definition flip_elim {τ} {x y:dom (dual τ)} (p:x ⊑ y) : (y:dom τ) ⊑ (x:dom τ) := p.

(***** qtype morphism *****)

Definition hom (τ₁:qtype) (τ₂:qtype) : qtype :=
  {| qdom := dom τ₁ r⇒ dom τ₂ |}.
Infix "⇒" := hom (at level 80, right associativity).

Definition QMorphism {τ₁ τ₂:qtype} (f:dom τ₁ -> dom τ₂) (p:proper (eqv v⇉ eqv) f) (m:proper (lte v⇉ lte) f) 
: dom (τ₁ ⇒ τ₂) := RFunction f p m.
Definition QMorphismA {τ₁ τ₂:qtype} (f:dom τ₁ -> dom τ₂) : dom (τ₁ ⇒ τ₂).
refine(QMorphism f _ _) ; admit.
Defined.
(*
Notation "'λ'  x .. y → e" := 
  (QMorphism (fun x => .. (QMorphism (fun y => e) _ _) ..) _ _)
  (x binder, y binder, at level 200, right associativity).
*)
Notation "'λ'  x .. y → e" := 
  (QMorphismA (fun x => .. (QMorphismA (fun y => e)) ..))
  (x binder, y binder, at level 200, right associativity).


Definition ap {τ₁ τ₂} : dom (τ₁ ⇒ τ₂) -> dom τ₁ -> dom τ₂ := rapply.
Infix "∙" := ap (at level 20, left associativity).
Infix "$" := ap (at level 99, right associativity, only parsing).

Definition respectful {τ₁ τ₂} 
(R1:relation (dom τ₁)) (R2:relation (dom τ₂)) (f g:dom (τ₁ ⇒ τ₂)) :=
  forall x y, R1 x y -> R2 (f ∙ x) (g ∙ y).
Arguments respectful : simpl never.
Infix "⇉" := respectful (at level 60, right associativity).

Definition qproper_intro {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} (p:(eqv ⇉ eqv) f g) : eqv f g := p.
Definition qproper_elim {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} (p:eqv f g) : (eqv ⇉ eqv) f g := p.
Definition qproper_apply {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} {x y:dom τ₁} (fp:f ≃ g) (xp:x ≃ y) 
: f ∙ x ≃ g ∙ y := fp x y xp.

Definition qmonotonic_intro {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} (p:(lte ⇉ lte) f g) : lte f g := p.
Definition qmonotonic_elim {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} (p:lte f g) : (lte ⇉ lte) f g := p.
Definition qmonotonic_apply {τ₁ τ₂} {f g:dom (τ₁ ⇒ τ₂)} {x y:dom τ₁} (fp:f ⊑ g) (xp:x ⊑ y) 
: f ∙ x ⊑ g ∙ y := fp x y xp.

Ltac qproper1 :=
  match goal with
  | [ |- ?x ≃ ?x ] => LibReflexivity
  | [ |- ?x ⊑ ?x ] => LibReflexivity
  | [ |- (eqv v⇉ eqv) _ _ ] => unfold vrespectful ; intros
  | [ |- (lte v⇉ lte) _ _ ] => unfold vrespectful ; intros
  | [ |- (eqv ⇉ eqv) _ _ ] => unfold respectful ; intros
  | [ |- (lte ⇉ lte) _ _ ] => unfold respectful ; intros
  | [ |- (λ _ → _) ≃ _ ] => apply qproper_intro ; unfold respectful ; intros ; simpl
  | [ |- _ ≃ (λ _ → _) ] => apply qproper_intro ; unfold respectful ; intros ; simpl
  | [ |- (λ _ → _) ⊑ _ ] => apply qmonotonic_intro ; unfold respectful ; intros ; simpl
  | [ |- _ ⊑ (λ _ → _) ] => apply qmonotonic_intro ; unfold respectful ; intros ; simpl
  | [ H : ?f ≃ ?g |- ?f ∙ _ ≃ ?g ∙ _ ] => apply H
  | [ H : ?f ⊑ ?g |- ?f ∙ _ ⊑ ?g ∙ _ ] => apply H
  | [ H : ?R ?x ?y |- ?R ?x ?y ] => exact H
  end.
Ltac qproper := repeat (simpl ; intros ; repeat qproper1).

Ltac qproper_elim :=
  repeat (
    simpl ; intros ; 
    repeat (
      qproper1 ||
      match goal with
      | [ |- _ ∙ _ ≃ _ ∙ _ ] => apply qproper_apply
      | [ |- _ ∙ _ ⊑ _ ∙ _ ] => apply qmonotonic_apply
      end)).

Definition id {τ₁} : dom (τ₁ ⇒ τ₁) := λ x → x.
Definition compose {τ₁ τ₂ τ₃} : dom ((τ₂ ⇒ τ₃) ⇒ (τ₁ ⇒ τ₂) ⇒ (τ₁ ⇒ τ₃)) :=
  λ g f x → g ∙ (f ∙ x).
Notation "g ⊙ f" := (compose ∙ g ∙ f) (at level 60, right associativity).
Definition const {τ₁ τ₂} : dom (τ₁ ⇒ τ₂ ⇒ τ₁) := λ x _ → x.
Definition applyTo {τ₁ τ₂} : dom (τ₁ ⇒ (τ₁ ⇒ τ₂) ⇒ τ₂) := λ x f → f ∙ x.
Definition apply {τ₁ τ₂} : dom ((τ₁ ⇒ τ₂) ⇒ τ₁ ⇒ τ₂) := λ f x → f ∙ x.