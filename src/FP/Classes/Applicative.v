Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Functor.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Data.Function_Q.
Require Import FP.Data.RewriteState.
Require Import FP.Data.RewriteState_T.

Import WeakSetoid.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.
Import RewriteState.Notation.

Class Applicative (t:WeakSetoid -> WeakSetoid) :=
  { fret :
      forall {A:WeakSetoid},
      DD (A ⇨ t A)
  ; fapply : 
      forall {A B:WeakSetoid}, 
      DD (t (A ⇨ B) ⇨ (t A ⇨ t B)) 
  ; applicative_identity : 
      forall (A:WeakSetoid), 
      fapply ⊛ (fret ⊛ (@id_Q A)) ≃ id_Q
  ; applicative_interchange :
      forall {A B:WeakSetoid} (fT:DD (t (A ⇨ B))) (x:DD A),
      fapply ⊛ fT ⊛ (fret ⊛ x) ≃ fapply ⊛ (fret ⊛ (apply_to_Q ⊛ x)) ⊛ fT
  ; applicative_homomorphism : 
      forall {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A), 
      fapply ⊛ (fret ⊛ f) ⊛ (fret ⊛ x) ≃ fret ⊛ (f ⊛ x)
  ; applicative_composition :
      forall {A B C:WeakSetoid} (g:DD (t (B ⇨ C))) (f:DD (t (A ⇨ B))),
      compose_Q ⊛ (fapply ⊛ g) ⊛ (fapply ⊛ f) 
      ≃ fapply ⊛ (fapply ⊛ (fapply ⊛ (fret ⊛ compose_Q) ⊛ g) ⊛ f)
  }.
Ltac R_Applicative_identity :=
  match goal with
  | [ |- RewriteState (fapply ⊛ (fret ⊛ (@id_Q ?A))) _ _ ] => ReplaceBy (applicative_identity A)
  end.
Ltac R_Applicative_interchange :=
  match goal with
  | [ |- RewriteState (fapply ⊛ ?fT ⊛ (fret ⊛ ?x)) _ _ ] => ReplaceBy (applicative_interchange fT x)
  end.
Ltac R_Applicative_homomorphism :=
  match goal with
  | [ |- RewriteState (fapply ⊛ (fret ⊛ ?f) ⊛ (fret ⊛ ?x)) _ _ ] => ReplaceBy (applicative_homomorphism f x)
  end.
Ltac R_Applicative_composition :=
  match goal with
  | [ |- RewriteState (compose_Q ⊛ (fapply ⊛ ?g) ⊛ (fapply ⊛ ?f)) _ _ ] => ReplaceBy (applicative_composition g f)
  end.
Ltac R_Applicative := 
  R_Applicative_identity || R_Applicative_homomorphism || R_Applicative_composition.

Section Applicative.
  Context {t:WeakSetoid -> WeakSetoid} `{! Applicative t }.

  Definition fapply_fmap {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ t A ⇨ t B) :=
    compose_Q ⊛ fapply ⊛ fret.

  Local Instance Applicative_To_Functor : Functor t := { fmap := @fapply_fmap }.
  Proof.
    Local Ltac Hammer := intros ; unfold fapply_fmap ; repeat Everywhere ltac:(R_Function_beta || R_Applicative).
    - Hammer.
    - Hammer.
  Defined.
End Applicative.

(*
Eval cbv iota beta delta 
  [functor_identity Applicative_To_Functor
   un_RewriteState mk_RewriteState
   rewrite_context_intro
   rewrite_context_elim
   rewrite_context_push_fun
   rewrite_context_push_arg
   rewrite_context_pop_fun
   rewrite_context_pop_arg
  ] 
in functor_identity (Functor:=Applicative_To_Functor).
*)