Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Eqv.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Type.
Require Import FP.Data.Tactic.

Import Relation.Notation.
Import Function.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Inductive WeakSetoid : Type := mk_WeakSetoid
  { WeakSetoid_T : Type
  ; WeakSetoid_WeakEqv : WeakEqv WeakSetoid_T
  }.
Existing Instance WeakSetoid_WeakEqv.

(* Embed a type with Leibniz equality *)
Definition EL (A:Type) : WeakSetoid := mk_WeakSetoid A (Leibniz_WeakEqv A).

(* Domain of definition for a weak setoid. *)
Inductive DD (A:WeakSetoid) : Type := mk_DD
  { DD_value : WeakSetoid_T A
  ; DD_proper : proper weqv DD_value
  }.
Arguments DD_value {A} _.
Arguments DD_proper {A} _.

(* Equivalence relation over values in DD *)
Instance DD_Eqv {A:WeakSetoid} : Eqv (DD A) :=
  { eqv x y := DD_value x ≈ DD_value y }.
Proof.
  - econstructor ; intros.
    apply (DD_proper x).
  - econstructor ; intros.
    Symmetry ; auto.
  - econstructor ; intros.
    Transitivity (DD_value y) ; auto.
Defined.
(* Induced weak equivalence *)
Instance DD_WeakEqv {A:WeakSetoid} : WeakEqv (DD A) := Eqv_WeakEqv.

Definition DD_value_respect {A:WeakSetoid} : proper weqv (DD_value (A:=A)) :=
  fun_respect_intro DD_value DD_value (fun _ _ xRy => xRy).

(* Arrows in the weak setoid universe *)
Definition weak_setoid_arrow (A B:WeakSetoid) : WeakSetoid :=
  mk_WeakSetoid (DD A -> DD B) Function_WeakEqv.
Local Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).

(* Application *)
Definition weak_setoid_apply {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A) : DD B :=
  mk_DD B (DD_value $ DD_value f $ x) (DD_proper f x x (DD_proper x)).
Local Infix "⊛" := weak_setoid_apply (left associativity, at level 50).

(* Lambdas *)
Definition mk_DD_f {A B:WeakSetoid} (f:DD A -> DD B) (p:proper weqv f) : DD (A ⇨ B) :=
  mk_DD (A ⇨ B) f p.
Local Notation "'λ?'  x .. y → e" := 
  (mk_DD_f (fun x => .. (mk_DD_f (fun y => e) _) ..) _)
  (right associativity, at level 200, x binder, y binder).

(* Respect introduction for _⇨_ *)
Definition weak_setoid_respect_intro {A B:WeakSetoid}
  {f g:DD (A ⇨ B)} (p:forall x y, x ≃ y -> f ⊛ x ≃ g ⊛ y)
  : f ≃ g := p.

(* Respect elimination for _⇨_ *)
Definition weak_setoid_respect_elim {A B:WeakSetoid} 
  {f g:DD (A ⇨ B)} (pf:f ≃ g) (x y:DD A) (px:x ≃ y)
  : f ⊛ x ≃ g ⊛ y := pf x y px.

(* Respect introduction for DD_value application *)
Definition DD_value_respect_intro {A B:WeakSetoid}
  {f g:DD (A ⇨ B)} (p:forall x y, x ≃ y -> f ⊛ x ≃ g ⊛ y)
  : DD_value f ≈ DD_value g := p.

(* Respect elimination for DD_value application *)
Definition DD_value_respect_elim {A B:WeakSetoid}
  {f g:DD (A ⇨ B)} (pf:f ≃ g) (x y:DD A) (px:x ≃ y)
  : DD_value f x ≃ DD_value g y := pf x y px.

(* Beta rule *)
Definition weak_setoid_beta {A B:WeakSetoid}
  (f:DD A -> DD B) (p:proper weqv f) (e:DD A)
  : mk_DD_f f p ⊛ e ≃ f e := p e e reflexivity.

Section Relation.
  Context {T} {R:relation T} `{! Symmetric R ,! Transitive R }.
  Definition replace_left {x y z} : R x y -> R y z -> R x z := transitivity y.
  Definition replace_right {x y z} : R y z -> R x z -> R x y := fun yRz xRz => transitivity z xRz (symmetry yRz).
End Relation.

Class ByDecideWeqv {A:WeakSetoid} (x:WeakSetoid_T A) : Type := 
  by_decide_weqv : proper weqv x.
Definition mk_DD_infer (A:WeakSetoid) (x:WeakSetoid_T A) `{! ByDecideWeqv x } : DD A :=
  mk_DD A x by_decide_weqv.
Definition mk_DD_infer_f {A B:WeakSetoid} (f:DD A -> DD B) `{! ByDecideWeqv (A:=A ⇨ B) f } : DD (A ⇨ B) :=
  mk_DD_f f $ by_decide_weqv (A:=A ⇨ B).

Ltac other_rule :=
  match goal with
    | [ |- (λ? _ → _) ≃ (λ? _ → _) ] =>
        eapply weak_setoid_respect_intro ; intros ;
        eapply (replace_left (weak_setoid_beta _ _ _)) ;
        eapply (replace_right (weak_setoid_beta _ _ _))
    end.

Ltac decide_weqv :=
  repeat (
    try Reflexivity ;
    unfold mk_DD_infer_f ;
    match goal with
    | [ |- ByDecideWeqv _ ] => unfold ByDecideWeqv
    | [ |- proper _ _ ] => unfold proper
    | [ |- ?x ≈ ?y ] => match type of x with DD _ => change (x ≃ y) end
    | [ |- (fun _ => _) ≈ (fun _ => _) ] => eapply fun_respect_intro ; intros ; simpl
    | [ |- (λ? _ → _) ≃ (λ? _ → _) ] =>
        eapply weak_setoid_respect_intro ; intros ;
        match goal with
        | [ |- ?e1 ≃ ?e2 ] =>
            let e1' := eval red in e1 in
            let e2' := eval red in e2 in
            change (e1' ≃ e2')
        end ; simpl
    | [ |- _ ⊛ _ ≃ _ ⊛ _ ] => eapply weak_setoid_respect_elim
    | [ |- _ ≃ _ ] => Reflexivity
    | [ |- {| DD_value := _ ; DD_proper := _ |} ≃ {| DD_value := _ ; DD_proper := _ |} ] => unfold_eqv ; simpl
    | [ |- DD_value _ ≈ DD_value _ ] => eapply fun_respect_elim
    | [ |- DD_value ≈ DD_value ] => eapply DD_value_respect
    | [ |- DD_value _ _ ≃ DD_value _ _ ] => eapply DD_value_respect_elim
    end) ; 
  auto.
Hint Extern 9 => (solve [ decide_weqv ]) : typeclass_instances.

Module Notation.
  Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).
  Infix "⊛" := weak_setoid_apply (left associativity, at level 50).
  Notation "'λ'  x .. y → e" := 
    (mk_DD_infer_f (fun x => .. (mk_DD_infer_f (fun y => e)) ..))
    (right associativity, at level 200, x binder, y binder).
  Notation "'λ?'  x .. y → e" := 
    (mk_DD_f (fun x => .. (mk_DD_f (fun y => e) _) ..) _)
    (right associativity, at level 200, x binder, y binder).
End Notation.