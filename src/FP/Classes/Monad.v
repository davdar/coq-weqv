Require Import FP.Data.WeakSetoid.
Require Import FP.Classes.WeakEqv.
Require Import FP.Data.Function_Q.
Require Import FP.Data.Unit.
Require Import FP.Data.Function.

Import Eqv.Notation.
Import WeakSetoid.Notation.
Import Unit.Notation.
Import Function.Notation.
Import WeakEqv.Notation.

Definition bind_associativity_k 
  {m:WeakSetoid -> WeakSetoid} (bind:forall {A B:WeakSetoid}, DD (m A ⇨ (A ⇨ m B) ⇨ m B)) 
  {A B C:WeakSetoid} (f:DD (A ⇨ m B)) (g:DD (B ⇨ m C))
  : DD (A ⇨ m C) := 
    mk_DD_infer (A ⇨ m C) 
                (fun x => DD_value bind (DD_value f x) (DD_value g)).

(* consider changing A ⇨ B to have DD A -> DD B as underlying type,
   rather than A -> B.  This is so arbitrary contexts (like the one
   created above, fun x => DD_value bind ...)  can give good beta
   rules.  After thinking about it, this sounds like the right way to
   go, and doesn't contradict anything I've built so far. *)

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
      ≃ bind ⊛ xM ⊛ bind_associativity_k (@bind) f g
  }.

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
      extend ⊛ k ⊛ (mplus ⊛ xM ⊛ yM) ≃ mplus ⊛ (extend ⊛ k ⊛ xM) ⊛ (extend ⊛ k ⊛ yM)
  }.