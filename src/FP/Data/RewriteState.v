Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Data.Function_Q.
Require Import FP.Data.Tactic.

Import WeakSetoid.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Create HintDb rewrite_beta.

Definition RewriteContext (A B:WeakSetoid) := DD (A ⇨ B).
Definition RCTop {A:WeakSetoid} : RewriteContext A A := id_Q.
Definition RCFocusFun {A B C:WeakSetoid} (k:DD (B ⇨ C)) (x:DD A) : RewriteContext (A ⇨ B) C :=
  compose_Q ⊛ k ⊛ (apply_to_Q ⊛ x).
Definition RCFocusArg {A B C:WeakSetoid} (k:DD (B ⇨ C)) (f:DD (A ⇨ B)) : RewriteContext A C :=
  compose_Q ⊛ k ⊛ (apply_Q ⊛ f).
                                                              
Definition RewriteState 
  {A B:WeakSetoid} (e:DD A) (k:RewriteContext A B) (g:DD B) 
  : Type := k ⊛ e ≃ g.
Opaque RewriteState.

Module Notation.
  Notation "κ⊤" := RCTop.
  Infix "◁" := RCFocusFun (at level 60, right associativity).
  Infix "▷" := RCFocusArg (at level 60, right associativity).
  Notation "【  f    ∈    c    ≃    g 】" := (RewriteState f c g).
End Notation.
Import Notation.

Definition rewrite_state_enter 
  {A:WeakSetoid} {e:DD A} {g:DD A} (p:RewriteState e κ⊤ g) 
  : e ≃ g := p.
Ltac Enter :=
  match goal with
  | [ |- ?e ≃ ?g ] => apply rewrite_state_enter
  end.
Ltac Enter0 :=
  match goal with
  | [ |- ?e ≃ ?g ] => change (RewriteState e κ⊤ g)
  end.

Definition rewrite_state_exit
  {A:WeakSetoid} {e:DD A} {g:DD A} (p:e ≃ g) 
  : RewriteState e RCTop g := p.
Ltac Exit :=
  match goal with
  | [ |- RewriteState ?e RCTop ?g ] => apply rewrite_state_exit
  end.
Ltac Exit0 :=
  match goal with
  | [ |- RewriteState ?e RCTop ?g ] => change (e ≃ g)
  end.

Definition rewrite_state_push_fun
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState f (k ◁ x) g)
  : RewriteState (f ⊛ x) k g := p.
Ltac PushFun :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply rewrite_state_push_fun
  end.
Ltac PushFun0 :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => change (RewriteState f (k ◁ x) g)
  end.

Definition rewrite_state_push_arg
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState x (k ▷ f) g)
  : RewriteState (f ⊛ x) k g := p.
Ltac PushArg :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply rewrite_state_push_arg
  end.
Ltac PushArg0 :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => change (RewriteState x (k ▷ f) g)
  end.

Definition rewrite_state_pop_fun
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState (f ⊛ x) k g)
  : RewriteState f (k ◁ x) g := p.
Definition rewrite_state_pop_arg
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState (f ⊛ x) k g)
  : RewriteState x (k ▷ f) g := p.
Ltac Pop :=
  match goal with
  | [ |- RewriteState ?f (?k ◁ ?x) ?g ] => apply rewrite_state_pop_fun
  | [ |- RewriteState ?x (?k ▷ ?f) ?g ] => apply rewrite_state_pop_arg
  end.
Ltac Pop0 :=
  match goal with
  | [ |- RewriteState ?f (?k ◁ ?x) ?g ] => change (RewriteState (f ⊛ x) k g)
  | [ |- RewriteState ?x (?k ▷ ?f) ?g ] => change (RewriteState (f ⊛ x) k g)
  end.

Ltac Escape := repeat Pop ; Exit.
Ltac Swap := try Escape ; Symmetry ; try Enter.

Definition rewrite_context_replace
  {A B:WeakSetoid} 
  {e:DD A} {e':DD A} (p:e ≃ e') {k:RewriteContext A B} {g:DD B} (rc:RewriteState e' k g)
  : RewriteState e k g.
Proof.
  change (k ⊛ e ≃ g) ; change (k ⊛ e' ≃ g) in rc.
  Transitivity (k ⊛ e') ; auto ; decide_weqv_beta.
Defined.

Ltac ReplaceBy q :=
  match goal with
  | [ |- RewriteState ?e ?k ?g ] => apply (rewrite_context_replace q)
  end.

Ltac ReplaceWith e' :=
  match goal with
  | [ |- RewriteState ?e ?k ?g ] => 
      let q := fresh "q" in
      refine (let q := (_ : e ≈ e') in rewrite_context_replace q _)
  end.

Ltac Everywhere_1 t :=
  match goal with
  | [ |- RewriteState (_ ⊛ _) _ _ ] =>
    chain PushFun ; Everywhere_1 t ; Pop |+|
    chain PushArg ; Everywhere_1 t ; Pop |+|
    t ; repeat t
  | _ => t ; repeat t
  end.

Ltac Everywhere t := 
  try (Enter ; Everywhere_1 t ; Exit) ;
  try (Symmetry ; Enter ; Everywhere_1 t ; Exit) ;
  try Reflexivity.

Ltac Everywhere_10 t :=
  match goal with
  | [ |- RewriteState (_ ⊛ _) _ _ ] =>
    chain PushFun0 ; Everywhere_10 t ; Pop0 |+|
    chain PushArg0 ; Everywhere_10 t ; Pop0 |+|
    t ; repeat t
  | _ => t ; repeat t
  end.

Ltac Everywhere0 t := 
  try (Enter0 ; Everywhere_10 t ; Exit0) ;
  try (Symmetry ; Enter0 ; Everywhere_10 t ; Exit0) ;
  try Reflexivity.