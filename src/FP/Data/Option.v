Require Import FP.Core.
Require Import FP.Classes.Monad.

Definition qoption : qtype -> qtype.
Admitted.

Definition qsome {A} : dom (A ⇒ qoption A).
Admitted.
Definition qnone {A} : dom (qoption A).
Admitted.
Definition qoption_elim {A B} : dom (qoption A ⇒ B ⇒ (A ⇒ B) ⇒ B).
Admitted.

Instance : Monad qoption.
Admitted.

Section MonadPlus.
  Context {m} `{! Monad m ,! MonadPlus m }.
  Definition liftOption {A} : dom (qoption A ⇒ m A) :=
    λ aO → qoption_elim ∙ aO ∙ mzero ∙ ret.
End MonadPlus.