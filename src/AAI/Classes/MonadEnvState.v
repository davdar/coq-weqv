Require Import FP.Classes.Monad.
Require Import FP.Data.Unit.
Require Import FP.Data.List.
Require Import FP.Data.Product.
Require Import FP.Data.Option.
Require Import FP.Core.

Definition env N L := qlist (N × L).

Class MonadEnvState N L m `{! Monad m } :=
  { getEnv : dom (m (env N L))
  ; putEnv : dom (env N L ⇒ m qunit)
  }.

Section MonadEnvState.
  Context {N L m} `{! Monad m ,! MonadEnvState N L m }.

  Definition modifyEnv : dom ((env N L ⇒ env N L) ⇒ m qunit) := λ f →
    e ← getEnv ;;
    putEnv $ f ∙ e.
  
  Definition lookupEnv `{! DecEqv (dom N) ,! MonadPlus m } : dom (N ⇒ m L) := λ n → 
    (liftOption ⊙ qlookup ∙ n) =<< getEnv.
End MonadEnvState.