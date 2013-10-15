Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Eqv.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Type.

Import Relation.Notation.
Import Function.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Inductive WeakSetoid : Type := mk_WeakSetoid
  { WeakSetoid_T : Type
  ; WeakSetoid_WeakEqv : WeakEqv WeakSetoid_T
  }.
Existing Instance WeakSetoid_WeakEqv.

Inductive DD (A:WeakSetoid) : Type := mk_DD
  { DD_value : WeakSetoid_T A
  ; DD_proper : proper weqv DD_value
  }.
Arguments DD_value {A} _.
Arguments DD_proper {A} _.

Instance DD_Eqv {A:WeakSetoid} : Eqv (DD A) :=
  { eqv x y := (DD_value x ≈ DD_value y) }.
Proof.
  - econstructor ; intros.
    apply (DD_proper x).
  - econstructor ; intros.
    Symmetry ; auto.
  - econstructor ; intros.
    Transitivity (DD_value y) ; auto.
Defined.

Definition weak_setoid_arrow (A B:WeakSetoid) : WeakSetoid :=
  mk_WeakSetoid (WeakSetoid_T A -> WeakSetoid_T B) Function_WeakEqv.
Local Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).

Definition weak_setoid_apply {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A) : DD B :=
  mk_DD B (DD_value f $ DD_value x) (DD_proper f (DD_value x) (DD_value x) (DD_proper x)).
Local Infix "⊛" := weak_setoid_apply (left associativity, at level 50).

Definition EL (A:Type) : WeakSetoid := mk_WeakSetoid A (Leibniz_WeakEqv A).

Ltac finish_decide_weqv_proper :=
  match goal with
  | [ |- ?f ?x ≈ ?g ?y ] => apply function_weqv_app ; finish_decide_weqv_proper
  | [ |- DD_value ?x ≈ DD_value ?x ] => exact (DD_proper x)
  | _ => tauto
  end.

Ltac decide_weqv_proper :=
  repeat
    (try finish_decide_weqv_proper ;
     match goal with
     | [ |- proper _ _ ] => unfold proper
     | [ |- ?f ≈ ?g ] =>
         match type of f with _ -> _ => 
           unfold "≈" ; simpl ; unfold respectful ; intros ; simpl
         end
     end).

Class ByDecideWeqv {A:WeakSetoid} (x:WeakSetoid_T A) : Type := 
  by_decide_weqv : proper weqv x.
Hint Extern 5 =>
  match goal with
  | [ |- ByDecideWeqv ?x ] => 
      unfold ByDecideWeqv ; decide_weqv_proper
  end : typeclass_instances.

Definition mk_DD_infer (A:WeakSetoid) (x:WeakSetoid_T A) `{! ByDecideWeqv x } : DD A :=
  mk_DD A x by_decide_weqv.

Ltac decide_weqv_beta :=
  repeat
    match goal with
    | [ |- ?x ≃ ?y ] =>
        match type of x with DD _ =>
          unfold "≃" ; simpl
        end
    | [ |- DD_value ?x ≈ DD_value ?x ] => apply (DD_proper x)
    | [ |- DD_value ?f _ ≈ DD_value ?f _ ] => apply (DD_proper f)
    end ;
  auto.

Module Notation.
  Infix "⇨" := weak_setoid_arrow (right associativity, at level 100).
  Infix "⊛" := weak_setoid_apply (left associativity, at level 50).
End Notation.