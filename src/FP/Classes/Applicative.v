Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Functor.
Require Import FP.Classes.Reflexive.
Require Import FP.Classes.Symmetric.
Require Import FP.Classes.Transitive.
Require Import FP.Data.Relation.
Require Import FP.Data.Function.
Require Import FP.Data.RewriteState.

Import WeakSetoid.Notation.
Import WeakEqv.Notation.
Import Eqv.Notation.

Class Applicative (t:WeakSetoid -> WeakSetoid) :=
  { fret :
      forall {A:WeakSetoid},
      DD (A ⇨ t A)
  ; fapply : 
      forall {A B:WeakSetoid}, 
      DD (t (A ⇨ B) ⇨ (t A ⇨ t B)) 
  ; applicative_identity : 
      forall {A:WeakSetoid}, 
      fapply ⊛ (fret ⊛ (idQ (A:=A))) ≃ idQ
  ; applicative_interchange :
      forall {A B:WeakSetoid} (fT:DD (t (A ⇨ B))) (x:DD A),
      fapply ⊛ fT ⊛ (fret ⊛ x) ≃ fapply ⊛ (fret ⊛ (apply_toQ ⊛ x)) ⊛ fT
  ; applicative_homomorphism : 
      forall {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A), 
      fapply ⊛ (fret ⊛ f) ⊛ (fret ⊛ x) ≃ fret ⊛ (f ⊛ x)
  ; applicative_composition :
      forall {A B C:WeakSetoid} (g:DD (t (B ⇨ C))) (f:DD (t (A ⇨ B))),
      composeQ ⊛ (fapply ⊛ g) ⊛ (fapply ⊛ f) 
      ≃ fapply ⊛ (fapply ⊛ (fapply ⊛ (fret ⊛ composeQ) ⊛ g) ⊛ f)
  }.

Section Applicative.
  Context {t:WeakSetoid -> WeakSetoid} `{! Applicative t }.

  Definition fapply_fmap {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ t A ⇨ t B) :=
    composeQ ⊛ fapply ⊛ fret.

  Local Instance Applicative_To_Functor : Functor t := { fmap := @fapply_fmap }.
  Proof.
    - intros ; unfold fapply_fmap.
      ReplaceBy (composeQ_elim fapply fret (idQ (A:=A))).
      ReplaceBy (applicative_identity (A:=A)).
      Exit ; Reflexivity.
    - intros ; unfold fapply_fmap.
      ReplaceBy (composeQ_elim fapply fret (composeQ ⊛ g ⊛ f)).
      Swap.
      PushFun ; PushArg.
        ReplaceBy (composeQ_elim fapply fret g).
      Pop ; Pop.
      PushArg.
        ReplaceBy (composeQ_elim fapply fret f).
      Pop.
      ReplaceBy (applicative_composition (fret ⊛ g) (fret ⊛ f)).
      PushArg ; PushFun ; PushArg.
        ReplaceBy (applicative_homomorphism (composeQ (A:=A)) g).
      Pop ; Pop ; Pop.
      PushArg.
        ReplaceBy (applicative_homomorphism (composeQ ⊛ g) f).
      Pop.
      Exit ; Reflexivity.
  Qed.
End Applicative.