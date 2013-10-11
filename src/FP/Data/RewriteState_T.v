Require Import FP.Data.Function_Q.
Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.Eqv.
Require Import FP.Classes.Transitive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Reflexive.
Require Import FP.Data.RewriteState.

Import Eqv.Notation.
Import RewriteState.Notation.
Import WeakSetoid.Notation.

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
  apply mk_RewriteState ; apply un_RewriteState in rc ; simpl in *.
  Transitivity (rewrite_context_interp (apply_to_Q ⊛ x ⊛ f) k) ; auto.
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
  apply mk_RewriteState ; apply un_RewriteState in rc ; simpl in *.
  Transitivity (rewrite_context_interp (apply_Q ⊛ f ⊛ x) k) ; auto.
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
  apply mk_RewriteState ; apply un_RewriteState in rc ; auto.
Defined.

Definition rewrite_context_pop_arg
  {A B C:WeakSetoid}
  (x:DD A) (f:DD (A ⇨ B)) (k:RewriteContext B C) (g:DD C)
  (rc:RewriteState (f ⊛ x) k g)
  : RewriteState x (k ▷ f) g.
Proof.
  apply mk_RewriteState ; apply un_RewriteState in rc ; auto.
Defined.

Ltac Pop :=
  match goal with
  | [ |- RewriteState ?f (?k ◁ ?x) ?g ] => apply (rewrite_context_pop_fun f x k g)
  | [ |- RewriteState ?x (?k ▷ ?f) ?g ] => apply (rewrite_context_pop_arg x f k g)
  end.

Ltac Escape := repeat Pop ; Exit.
Ltac Swap := Escape ; Symmetry ; Enter.

Ltac Everywhere_1 t :=
  try Enter ;
  match goal with
  | [ |- RewriteState (_ ⊛ _) _ _ ] =>
      PushFun ; Everywhere_1 t ; Pop ; PushArg ; Everywhere_1 t ; Pop ; repeat t
  | _ => repeat t
  end ;
  try Exit ;
  try Reflexivity.

Ltac Everywhere t := Everywhere_1 t ; Symmetry ; Everywhere_1 t ; Symmetry.