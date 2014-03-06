Require Import FP.Classes.Monad.
Require Import FP.Data.Unit.
Require Import FP.Data.List.
Require Import FP.Data.Product.
Require Import FP.Data.Option.
Require Import FP.Core.

Definition store (D:qtype -> qtype) L V := qlist (L × D V).

Class MonadStoreState D L V m :=
  { getStore : dom (m (store D L V))
  ; putStore : dom (store D L V ⇒ m unit)
  }.

Section MonadStoreState.
  Context {D L V m} `{! Monad m ,! MonadStoreState D L V m }.

  Definition modifyStore : dom ((store D L V ⇒ store D L V) ⇒ m unit) := λ f →
    e ← getStore ;;
    putStore $ f ∙ e.
  
  Definition lookupStore `{! DecEqv (dom L) ,! MonadPlus m } : dom (L ⇒ m (D V)) := λ n → 
    (liftOption ⊙ qlookup ∙ n) =<< getStore.
End MonadStoreState.