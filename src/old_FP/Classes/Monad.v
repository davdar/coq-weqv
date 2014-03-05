Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Applicative.
Require Import FP.Classes.Eqv.
Require Import FP.Data.Function_Q.
Require Import FP.Data.Relation.
Require Import FP.Data.Unit.
Require Import FP.Data.Function.
Require Import FP.Data.RewriteState.

Import Eqv.Notation.
Import WeakSetoid.Notation.
Import Unit.Notation.
Import Function.Notation.
Import WeakEqv.Notation.
Import RewriteState.Notation.

Class Monad (m:WeakSetoid -> WeakSetoid) : Type :=
  { ret : 
      forall {A:WeakSetoid}, 
      DD (A ⇨ m A)
  ; bind : forall {A B:WeakSetoid}, 
      DD (m A ⇨ (A ⇨ m B) ⇨ m B)
  ; monad_left_unit : 
      forall {A:WeakSetoid} (xM:DD (m A)), 
      bind ⊛ xM ⊛ ret ≃ xM
  ; monad_right_unit : 
      forall {A B:WeakSetoid} (x:DD A) (k:DD (A ⇨ m B)), 
      bind ⊛ (ret ⊛ x) ⊛ k ≃ k ⊛ x
  ; monad_associativity :
      forall {A B C:WeakSetoid} (xM:DD (m A)) (f:DD (A ⇨ m B)) (g:DD (B ⇨ m C)),
      bind ⊛ (bind ⊛ xM ⊛ f) ⊛ g 
      ≃ bind ⊛ xM ⊛ (λ x → bind ⊛ (f ⊛ x) ⊛ g)
  }.
Ltac R_Monad_left_unit :=
  match goal with
  | [ |- RewriteState (bind ⊛ ?xM ⊛ ret) _ _ ] => ReplaceBy (monad_left_unit xM)
  end.
Ltac R_Monad_right_unit :=
  match goal with
  | [ |- RewriteState (bind ⊛ (ret ⊛ ?x) ⊛ ?k) _ _ ] => ReplaceBy (monad_right_unit x k)
  end.
Ltac R_Monad_associativity :=
  match goal with
  | [ |- RewriteState (bind ⊛ (bind ⊛ ?xM ⊛ ?f) ⊛ ?g) _ _ ] => ReplaceBy (monad_associativity xM f g)
  end.
Ltac R_Monad := R_Monad_left_unit || R_Monad_right_unit || R_Monad_associativity.

Section Monad.
  Context {m:WeakSetoid -> WeakSetoid} `{! Monad m }.
  
  Definition monad_fapply {A B:WeakSetoid} : DD (m (A ⇨ B) ⇨ m A ⇨ m B) :=
    λ fM → λ xM → bind ⊛ fM ⊛ (λ f → bind ⊛ xM ⊛ (λ x → ret ⊛ (f ⊛ x))).
  
  Local Instance Monad_To_Applicative : Applicative m := { fret := @ret _ _ ; fapply := @monad_fapply }.
  Proof.
    Local Ltac Hammer := 
      intros ; unfold monad_fapply,fret,mk_DD_infer_f ;
      repeat Everywhere ltac:(R_fun_beta || R_Monad).
    - Hammer.

      
      unfold_eqv ; unfold_weqv ; unfold respectful ; intros.
      e1 ≈ e1
      λ x → e1 ≈ λ x → e2
      intros ; unfold monad_fapply,fret,mk_DD_infer_f.
      unfold "≃" ; simpl.
      decide_weqv.
      Hammer.
      Enter.
      R_beta.
      PushFun.
      Hammer.
End Monad.

Class MonadState (S:WeakSetoid) (m:WeakSetoid -> WeakSetoid) : Type :=
  { get : DD (m S)
  ; put : DD (S ⇨ m (EL ⊤))
  }.

Class MonadPlus (m:WeakSetoid -> WeakSetoid) `{! Monad m } : Type :=
  { mplus : 
      forall {A:WeakSetoid}, 
      DD (m A ⇨ m A ⇨ m A) 
  ; monad_plus_distributivity : 
      forall {A B:WeakSetoid} (xM yM:DD (m A)) (k:DD (A ⇨ m B)), 

  }.