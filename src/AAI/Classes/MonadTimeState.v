Require Import FP.Core.
Require Import FP.Classes.Monad.
Require Import FP.Data.Unit.


Class MonadTimeState T m :=
  { getTime : dom (m T)
  ; putTime : dom (T ⇒ m qunit)
  }.

Section MonadTimeState.
  Context {T m} `{! Monad m ,! MonadTimeState T m }.

  Definition modifyTime : dom ((T ⇒ T) ⇒ m qunit) := λ f →
    e ← getTime ;;
    putTime $ f ∙ e.
End MonadTimeState.