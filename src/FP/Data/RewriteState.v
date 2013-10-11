Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Functor.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.

Import WeakSetoid.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

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
Local Notation "κ⊤" := RCTop.
Local Infix "◁" := RCFocusFun (at level 60, right associativity).
Local Infix "▷" := RCFocusArg (at level 60, right associativity).

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

Inductive RewriteState 
  {A B:WeakSetoid} 
  (focus:DD A) (context:RewriteContext A B) (goal:DD B) : Type := mk_RewriteState
  { rewrite_state_p : rewrite_context_interp focus context ≃ goal
  }.
Arguments mk_RewriteState {A B} focus context goal rewrite_state_p.
Local Notation "【  f    ∈    c    ≈    g 】" := (RewriteState f c g).

Definition rewrite_context_elim {A:WeakSetoid} (e:DD A) (g:DD A) (rc:RewriteState e κ⊤ g) : e ≃ g.
Proof.
  destruct rc ; simpl in * ; auto.
Defined.

Ltac Enter :=
  match goal with
  | [ |- ?x ≃ ?y ] => apply (rewrite_context_elim x y)
  end.

Definition rewrite_context_intro 
  {A:WeakSetoid} (e:DD A) (g:DD A) (q:e ≃ g)
  : RewriteState e κ⊤ g := mk_RewriteState e κ⊤ g q.

Ltac Exit :=
  match goal with
  | [ |- RewriteState ?e κ⊤ ?g ] => 
      apply (rewrite_context_intro e g)
  end.

Definition rewrite_context_push_fun
  {A B C:WeakSetoid} 
  (f:DD (A ⇨ B)) (x:DD A) (k:RewriteContext B C) (g:DD C) 
  (rc:RewriteState f (k ◁ x) g)
  : RewriteState (f ⊛ x) k g.
Proof.
  destruct rc ; constructor ; simpl in *.
  Transitivity (rewrite_context_interp (apply_toQ ⊛ x ⊛ f) k) ; auto.
  apply rewrite_context_respect_weqv ; decide_weqv.
Defined.

Ltac PushFun :=
  try Enter ;
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply (rewrite_context_push_fun f x k g)
  end.

Definition rewrite_context_push_arg
  {A B C:WeakSetoid} 
  (f:DD (A ⇨ B)) (x:DD A) (k:RewriteContext B C) (g:DD C) 
  (rc:RewriteState x (k ▷ f) g)
  : RewriteState (f ⊛ x) k g.
Proof.
  destruct rc ; constructor ; simpl in *.
  Transitivity (rewrite_context_interp (applyQ ⊛ f ⊛ x) k) ; auto.
  apply rewrite_context_respect_weqv ; decide_weqv.
Defined.

Ltac PushArg :=
  try Enter ;
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply (rewrite_context_push_arg f x k g)
  end.

Definition rewrite_context_pop_fun
  {A B C:WeakSetoid}
  (f:DD (A ⇨ B)) (x:DD A) (k:RewriteContext B C) (g:DD C)
  (rc:RewriteState (f ⊛ x) k g)
  : RewriteState f (k ◁ x) g.
Proof.
  destruct rc ; constructor ; auto.
Qed.

Definition rewrite_context_pop_arg
  {A B C:WeakSetoid}
  (x:DD A) (f:DD (A ⇨ B)) (k:RewriteContext B C) (g:DD C)
  (rc:RewriteState (f ⊛ x) k g)
  : RewriteState x (k ▷ f) g.
Proof.
  destruct rc ; constructor ; auto.
Qed.

Ltac Pop :=
  match goal with
  | [ |- RewriteState ?f (?k ◁ ?x) ?g ] => apply (rewrite_context_pop_fun f x k g)
  | [ |- RewriteState ?x (?k ▷ ?f) ?g ] => apply (rewrite_context_pop_arg x f k g)
  end.

Ltac Escape := repeat Pop ; Exit.
Ltac Swap := Escape ; Symmetry ; Enter.

Definition rewrite_context_replace
  {A B:WeakSetoid} 
  (e:DD A) (e':DD A) (p:e ≃ e') (k:RewriteContext A B) (g:DD B) (rc:RewriteState e' k g)
  : RewriteState e k g.
Proof.
  destruct rc ; constructor.
  Transitivity (rewrite_context_interp e' k) ; auto.
  apply rewrite_context_respect_weqv ; auto.
Defined.

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
