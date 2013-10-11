Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.

Import WeakSetoid.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Create HintDb rewrite_beta.

(* Also make this a definition := it's interp, constructors are just opaque things *)
Inductive RewriteContext : WeakSetoid -> WeakSetoid -> Type :=
  | RCTop : forall {A}, RewriteContext A A
  | RCFocusFun : 
      forall {A B C:WeakSetoid}, 
      RewriteContext B C -> DD A -> RewriteContext (A ⇨ B) C
  | RCFocusArg : 
      forall {A B C:WeakSetoid}, 
      RewriteContext B C -> DD (A ⇨ B) -> RewriteContext A C.
Arguments RCTop {A}.
Arguments RCFocusFun {A B C} _ _.
Arguments RCFocusArg {A B C} _ _.

Definition rewrite_context_interp {A B:WeakSetoid} (e:DD A) (k:RewriteContext A B) : DD B.
Proof.
  induction k ; auto. 
  apply IHk ; exact (e ⊛ d).
  apply IHk ; exact (d ⊛ e).
Defined.

Definition rewrite_context_respect_weqv 
  {A B:WeakSetoid} 
  (x y:DD A) (p:x ≃ y) (rc:RewriteContext A B) 
  : rewrite_context_interp x rc ≃ rewrite_context_interp y rc.
Proof.
  induction rc ; simpl in * ; auto.
  - apply IHrc ; decide_weqv.
  - apply IHrc ; decide_weqv.
Defined.

Definition RewriteState 
  {A B:WeakSetoid} 
  (e:DD A) (k:RewriteContext A B) (g:DD B) : Type := rewrite_context_interp e k ≃ g.
Definition mk_RewriteState 
  {A B:WeakSetoid}
  (e:DD A) (k:RewriteContext A B) (g:DD B) 
  (p:rewrite_context_interp e k ≃ g)
  : RewriteState e k g := p.
Definition un_RewriteState 
  {A B:WeakSetoid}
  (e:DD A) (k:RewriteContext A B) (g:DD B) 
  (rs:RewriteState e k g)
  : rewrite_context_interp e k ≃ g := rs.
Opaque RewriteState.

Definition rewrite_context_replace
  {A B:WeakSetoid} 
  (e:DD A) (e':DD A) (p:e ≃ e') (k:RewriteContext A B) (g:DD B) (rc:RewriteState e' k g)
  : RewriteState e k g.
Proof.
  apply mk_RewriteState ; apply un_RewriteState in rc.
  Transitivity (rewrite_context_interp e' k) ; auto.
  apply rewrite_context_respect_weqv ; auto.
Defined.

Definition rewrite_context_elim {A:WeakSetoid} (e:DD A) (g:DD A) (rc:RewriteState e RCTop g) : e ≃ g.
Proof.
  apply un_RewriteState in rc ; simpl in * ; auto.
Defined.

Ltac Enter :=
  match goal with
  | [ |- ?x ≃ ?y ] => apply (rewrite_context_elim x y)
  end.

Ltac ReplaceBy q :=
  try Enter ;
  match goal with
  | [ |- RewriteState ?e ?k ?g ] => apply (rewrite_context_replace e _ q k g)
  end.

Ltac ReplaceWith e' :=
  try Enter ;
  match goal with
  | [ |- RewriteState ?e ?k ?g ] => 
      let q := fresh "q" in
      refine (let q := (_ : e ≈ e') in rewrite_context_replace e e' q k g _)
  end.

Module Notation.
  Notation "κ⊤" := RCTop.
  Infix "◁" := RCFocusFun (at level 60, right associativity).
  Infix "▷" := RCFocusArg (at level 60, right associativity).
  Notation "【  f    ∈    c    ≃    g 】" := (RewriteState f c g).
End Notation.