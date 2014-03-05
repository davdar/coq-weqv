Require Import FP.Core.
Require Import FP.Classes.Monad.

Class Traversable (t:qtype -> qtype) :=
  { traverse : forall {m A B} `{! Monad m }, dom ((A ⇒ m B) ⇒ (t A ⇒ m (t B))) }.

Section Traversable.
  Context {t} `{! Traversable t }.
  
  Definition sequence {m A} `{! Monad m } : dom (t (m A) ⇒ m (t A)) := traverse ∙ id.
End Traversable.