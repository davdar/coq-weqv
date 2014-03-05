Require Import FP.Core.Relations.

Inductive rfunction A B `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } := RFunction
  { rfun : A -> B
  ; rfun_proper : proper (eqv v⇉ eqv) rfun
  ; rfun_monotonic : proper (lte v⇉ lte) rfun
  }.
Arguments RFunction {A B _ _ _ _} _ _ _.
Arguments rfun {A B _ _ _ _} _ _.
Arguments rfun_proper {A B _ _ _ _} _ x y _.
Arguments rfun_monotonic {A B _ _ _ _} _ x y _.
Infix "r⇒" := rfunction (at level 60, right associativity).
Notation "'rλ'  x .. y → e" := 
  (RFunction (fun x => .. (RFunction (fun y => e) _ _) ..) _ _)
  (x binder, y binder, at level 200, right associativity).

Definition rapply {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (f:A r⇒ B) (x:A) : B := rfun f x.
Infix "r∙" := rapply (at level 20, left associativity).

Definition rrespectful {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (R1:relation A) (R2:relation B) (f g:A r⇒ B) :=
  forall x y, R1 x y -> R2 (f r∙ x) (g r∙ y).
Infix "r⇉" := rrespectful (at level 60, right associativity).

Ltac rproper1 :=
  match goal with
  | [ |- ?x ≃ ?x ] => LibReflexivity
  | [ |- ?x ⊑ ?x ] => Reflexivity ; LibReflexivity
  | [ |- ?f r∙ _ ≃ ?f r∙ _ ] => apply (rfun_proper f)
  | [ |- ?f r∙ _ ⊑ ?f r∙ _ ] => apply (rfun_monotonic f)
  | [ |- (eqv v⇉ eqv) _ _ ] => unfold vrespectful ; intros
  | [ |- (lte v⇉ lte) _ _ ] => unfold vrespectful ; intros
  | [ |- (eqv r⇉ eqv) _ _ ] => unfold rrespectful ; intros
  | [ |- (lte r⇉ lte) _ _ ] => unfold rrespectful ; intros
  | [ H : ?f ≃ ?g |- ?f r∙ _ ≃ ?g r∙ _ ] => apply H
  | [ H : ?f ⊑ ?g |- ?f r∙ _ ⊑ ?g r∙ _ ] => apply H
  | [ H : (eqv r⇉ eqv) ?f ?g |- ?f r∙ _ ≃ ?g r∙ _ ] => apply H
  | [ H : (lte r⇉ lte) ?f ?g |- ?f r∙ _ ⊑ ?g r∙ _ ] => apply H
  | [ H : ?R ?x ?y |- ?R ?x ?y ] => exact H
  end.
Ltac rproper := repeat (simpl ; intros ; repeat rproper1).

Instance : forall A B `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B }, Eqv (A r⇒ B) :=
  { eqv := (eqv r⇉ eqv) }.
Proof.
  constructor ; rproper.
  - Symmetry ; rproper ; Symmetry ; rproper.
  - Transitivity (y r∙ x0) ; rproper.
Defined.

Instance : forall A B `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B }, Lte (A r⇒ B) :=
  { lte := (lte r⇉ lte) }.
Proof.
  constructor ; rproper.
  - Transitivity (y r∙ x0) ; rproper.
    Reflexivity ; rproper.
  - Transitivity (y r∙ x0) ; rproper.
Defined.

Definition rproper_intro {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (f g:A r⇒ B) (p:(eqv r⇉ eqv) f g)
: eqv f g := p.
Definition rproper_elim {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (f g:A r⇒ B) (p:eqv f g) 
: (eqv r⇉ eqv) f g := p.

Definition rmonotonic_intro {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (f g:A r⇒ B) (p:(lte r⇉ lte) f g)
: lte f g := p.
Definition rmonotonic_elim {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } (f g:A r⇒ B) (p:lte f g) 
: (lte r⇉ lte) f g := p.

Ltac rproper2 :=
  rproper1 ||
  match goal with
  | [ |- (rλ _ → _) ≃ _ ] => apply rproper_intro ; unfold "r⇉" ; intros ; simpl
  | [ |- _ ≃ (rλ _ → _) ] => apply rproper_intro ; unfold "r⇉" ; intros ; simpl
  | [ |- (rλ _ → _) ⊑ _ ] => apply rmonotonic_intro ; unfold "r⇉" ; intros ; simpl
  | [ |- _ ⊑ (rλ _ → _) ] => apply rmonotonic_intro ; unfold "r⇉" ; intros ; simpl
  end.
Ltac rproper ::= repeat (simpl ; intros ; repeat rproper2).

Ltac rproper_elim :=
  repeat
  match goal with
  | [ |- _ r∙ _ ≃ _ r∙ _ ] => apply rproper_elim
  | [ |- _ r∙ _ ⊑ _ r∙ _ ] => apply rmonotonic_elim
  end.

Definition rcompose {A B C} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B ,! Eqv C ,! Lte C } 
: ((B r⇒ C) r⇒ (A r⇒ B) r⇒ (A r⇒ C)). 
refine( rλ g f x → g r∙ (f r∙ x) ) ; rproper.
Grab Existential Variables. rproper. rproper. rproper. rproper.
Defined.
Infix "r⊙" := rcompose (at level 60, right associativity).

Definition rid {A} `{! Eqv A ,! Lte A } : A r⇒ A.
refine( rλ x → x ) ; rproper.
Defined.
Definition rconst {A B} `{! Eqv A ,! Lte A ,! Eqv B ,! Lte B } : A r⇒ B r⇒ A.
refine( rλ y _ → y ) ; rproper.
Grab Existential Variables. rproper. rproper.
Defined.