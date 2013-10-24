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

(*
Inductive RewriteContext : WeakSetoid -> WeakSetoid -> Type :=
  | RCTop : forall {A}, RewriteContext A A
  | RCFocusFun : forall {A B C}, RewriteContext B C -> DD A -> RewriteContext (A ⇨ B) C
  | RCFocusArg : forall {A B C}, RewriteContext B C -> DD (A ⇨ B) -> RewriteContext A C.
*)

Definition RewriteContext (A B:WeakSetoid) := DD (A ⇨ B).
Definition RCTop {A:WeakSetoid} : RewriteContext A A := id_Q.
Definition RCFocusFun {A B C:WeakSetoid} (x:DD A) (k:DD (B ⇨ C)) : RewriteContext (A ⇨ B) C :=
  compose_Q ⊛ k ⊛ (apply_to_Q ⊛ x).
Definition RCFocusArg {A B C:WeakSetoid} (f:DD (A ⇨ B)) (k:DD (B ⇨ C)) : RewriteContext A C :=
  compose_Q ⊛ k ⊛ (apply_Q ⊛ f).

(*
Definition RewriteContext_interp {A B:WeakSetoid} (k:RewriteContext A B) (x:DD A) : DD B.
Proof.
  induction k.
  - exact x.
  - exact (IHk (x ⊛ d)).
  - exact (IHk (d ⊛ x)).
Defined.
*)
                                                              
(*
Inductive RewriteState {A B} (e:DD A) (k:RewriteContext A B) (g:DD B) : Type :=
  | mk_RewriteState : RewriteContext_interp k e ≃ g -> RewriteState e k g.
*)

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
(*
Proof.
  destruct p ; auto.
Defined.
*)
Ltac Enter :=
  match goal with
  | [ |- ?e ≃ ?g ] => apply rewrite_state_enter
  end.
Ltac EnterDNL :=
  match goal with
  | [ |- ?e ≃ ?g ] => change (RewriteState e κ⊤ g)
  end.

Definition rewrite_state_exit
  {A:WeakSetoid} {e:DD A} {g:DD A} (p:e ≃ g) 
  : RewriteState e RCTop g := p.
(*
Proof.
  constructor ; auto.
Defined.
*)
Ltac Exit :=
  match goal with
  | [ |- RewriteState ?e κ⊤ ?g ] => apply rewrite_state_exit
  end.
Ltac ExitDNL :=
  match goal with
  | [ |- RewriteState ?e κ⊤ ?g ] => change (e ≃ g)
  end.

Definition rewrite_state_push_fun
  {A B C:WeakSetoid} 
  (f:DD (A ⇨ B)) (x:DD A) (k:RewriteContext B C) (g:DD C)
  (p:RewriteState f (x ◁ k) g)
  : RewriteState (f ⊛ x) k g := p.
(*
Proof.
  constructor ; destruct p ; auto.
Defined.
*)
Ltac PushFun :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply (rewrite_state_push_fun f x k g)
  end.
Ltac PushFunDNL :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => change (RewriteState f (x ◁ k) g)
  end.

Definition rewrite_state_push_arg
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState x (f ▷ k) g)
  : RewriteState (f ⊛ x) k g := p.
(*
Proof.
  constructor ; destruct p ; auto.
Defined.
*)
Ltac PushArg :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => apply rewrite_state_push_arg
  end.
Ltac PushArgDNL :=
  match goal with
  | [ |- RewriteState (?f ⊛ ?x) ?k ?g ] => change (RewriteState x (f ▷ k) g)
  end.

Definition rewrite_state_pop_fun
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState (f ⊛ x) k g)
  : RewriteState f (x ◁ k) g := p.
(*
Proof.
  constructor ; inversion p ; auto.
Defined.
*)
Definition rewrite_state_pop_arg
  {A B C:WeakSetoid} {f:DD (A ⇨ B)} {x:DD A} {k:RewriteContext B C} {g:DD C}
  (p:RewriteState (f ⊛ x) k g)
  : RewriteState x (f ▷ k) g := p.
(*
Proof.
  constructor ; destruct p ; auto.
Defined.
*)
Ltac Pop :=
  match goal with
  | [ |- RewriteState ?f (?x ◁ ?k) ?g ] => apply rewrite_state_pop_fun
  | [ |- RewriteState ?x (?f ▷ ?k) ?g ] => apply rewrite_state_pop_arg
  end.
Ltac PopDNL :=
  match goal with
  | [ |- RewriteState ?f (?x ◁ ?k) ?g ] => change (RewriteState (f ⊛ x) k g)
  | [ |- RewriteState ?x (?f ▷ ?k) ?g ] => change (RewriteState (f ⊛ x) k g)
  end.

Ltac Escape := repeat Pop ; Exit.
Ltac EscapeDNL := repeat PopDNL ; ExitDNL.

Definition rewrite_context_replace
  {A B:WeakSetoid} 
  {e:DD A} {e':DD A} (p:e ≃ e') {k:RewriteContext A B} {g:DD B} (rc:RewriteState e' k g)
  : RewriteState e k g.
Proof.
  change (k ⊛ e ≃ g).
  Transitivity (k ⊛ e') ; auto.
  decide_weqv.
Defined.
(*
Proof.
  constructor ; destruct rc ; induction k ; simpl in *.
  - Transitivity e' ; auto.
  - eapply IHk.
    eapply weak_setoid_respect_elim.
    apply p.
    Reflexivity.
    auto.
  - eapply IHk.
    eapply weak_setoid_respect_elim.
    Reflexivity.
    apply p.
    auto.
Defined.
*)
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

Ltac Everywhere_1_DNL t :=
  match goal with
  | [ |- RewriteState (_ ⊛ _) _ _ ] =>
    chain PushFunDNL ; Everywhere_1_DNL t ; PopDNL |+|
    chain PushArgDNL ; Everywhere_1_DNL t ; PopDNL |+|
    t ; repeat t
  | _ => t ; repeat t
  end.
Ltac EverywhereDNL t := 
  try (EnterDNL ; Everywhere_1_DNL t ; ExitDNL) ;
  try (Symmetry ; EnterDNL ; Everywhere_1_DNL t ; ExitDNL) ;
  try Reflexivity.

Ltac R_beta :=
  match goal with
  | [ |- RewriteState (mk_DD_f ?f ?p ⊛ ?e) _ _ ] => ReplaceBy (weak_setoid_beta f p e)
  end.

Ltac R_fun :=
  match goal with
  | [ |- RewriteState (compose_Q ⊛ ?g ⊛ ?f ⊛ ?x) _ _ ] => 
      unfold_in_term compose_Q (compose_Q ⊛ g ⊛ f ⊛ x) ; unfold mk_DD_infer_f
  | [ |- RewriteState (id_Q ⊛ ?x) _ _ ] => 
      unfold_in_term id_Q (id_Q ⊛ x) ; unfold mk_DD_infer_f
  end.

Ltac R_fun_beta := R_fun || R_beta.