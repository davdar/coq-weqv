Require Import FP.Core.
Require Import FP.Classes.Monad.
Require Import AAI.Classes.MonadTimeState.

Class Addressable (V T L:qtype) :=
  { alloc : dom (V ⇒ T ⇒ L) }.

Section Addressable.
  Context {V T L m} 
  `{! Monad m ,! MonadTimeState T m ,! Addressable V T L }.
  
  Definition new : dom (V ⇒ m L) := λ v →
    t ← getTime ;;
    ret $ alloc ∙ v ∙ t.
End Addressable.