Require Import AAI.Classes.MonadEnvState.
Require Import AAI.Classes.MonadStoreState.
Require Import AAI.Classes.MonadTimeState.
Require Import AAI.Classes.Addressable.
Require Import AAI.Classes.Transition.
Require Import FP.Core.
Require Import FP.Data.String.
Require Import FP.Data.List.
Require Import FP.Data.Option.
Require Import FP.Data.Product.
Require Import FP.Classes.Monad.
Require Import FP.Classes.Traversable.
Require Import FP.Classes.Peano.

Inductive Op := Add1 | Sub1.

Inductive Call :=
  | IfZC (a:Atom) (tc:Call) (fc:Call)
  | LamAppC (f:Atom) (x:Atom) (k:Atom)
  | KonAppC (k:Atom) (x:Atom)
  | HaltC (a:Atom)
with Atom :=
  | LitA (n:nat)
  | VarA (x:dom string)
  | LamA (x:dom string) (k:dom string) (c:Call)
  | KonA (x:dom string) (c:Call)
  | PrimA (o:Op) (args:vlist Atom).

Inductive Val L :=
  | NumV (n:nat)
  | NatV
  | LamCloV (x:dom string) (k:dom string) (c:dom (lib Call)) (env:dom (env string L))
  | KonCloV (x:dom string) (c:dom (lib Call)) (env:dom (env string L)).
Arguments NumV {L} n.
Arguments NatV {L}.
Arguments LamCloV {L} x k c env.
Arguments KonCloV {L} x c env.

(* Variable names and their meanings:
   - m : the interpretation monad 
   - d : the domain of the state space
   - L : location
   - T : time 
*)
Class Analysis (d:qtype -> qtype) (L:qtype) (T:qtype) (m:qtype -> qtype) :=
  { Analysis_d_Monad           :> Monad d
  ; Analysis_d_Traversable     :> Traversable d
  ; Analysis_L_DecEq           :> DecEqv (dom L)
  ; Analysis_T_Peano           :> Peano T
  ; Analysis_T_Addressable     :> Addressable string T L
  ; Analysis_m_Monad           :> Monad m
  ; Analysis_m_MonadPlus       :> MonadPlus m
  ; Analysis_m_MonadMorphism   :> MonadMorphism d m
  ; Analysis_m_MonadEnvState   :> MonadEnvState string L m
  ; Analysis_m_MonadStoreState :> MonadStoreState d L (lib (Val L)) m
  ; Analysis_m_MonadTimeState  :> MonadTimeState T m
  }.

Section S.
  Context {d L T m} `{! Analysis d L T m }.
  Context (delt:dom (lib Op ⇒ list (lib (Val L)) ⇒ qoption (lib (Val L)))). 
  
  Definition coerceLamCloV : dom (lib (Val L) ⇒ m (string × string × lib Call × env string L)) := 
    λ (x : dom (lib (Val L))) →
      match x with
      | LamCloV x k c ρ => ret ∙ (x ,, k ,, c ,, ρ)
      | _ => mzero
      end.

  Definition coerceKonCloV : dom (lib (Val L) ⇒ m (string × lib Call × env string L)) :=
    λ (x : dom (lib (Val L))) →
      match x with
      | KonCloV x c ρ => ret ∙ (x ,, c ,, ρ)
      | _ => mzero
      end.

  Fixpoint _atomic (a:Atom) : dom (m (d (lib (Val L)))) :=
    match a with
    | LitA n => ret (m:=m) $ ret (m:=d) $ (NumV n : dom (lib (Val L)))
    | VarA x =>
        a ← lookupEnv ∙ x ;;
        lookupStore ∙ a
    | LamA x k c =>
        env ← getEnv ;;
        ret (m:=m) $ ret (m:=d) $ (LamCloV x k c env : dom (lib (Val L)))
    | KonA x c =>
        env ← getEnv ;;
        ret (m:=m) $ ret (m:=d) $ (KonCloV x c env : dom (lib (Val L)))
    | PrimA o args =>
        let vDMs : dom (list (m (d (lib (Val L))))) := vlmap _atomic args in
        vDs ← sequence ∙ vDMs ;;
        let vsD : dom (d (list (lib (Val L)))) := sequence (t:=list) (m:=d) ∙ vDs in
        let vMD : dom (d (qoption (lib (Val L)))) := mmap (m:=d) ∙ (delt ∙ o) ∙ vsD in
        liftOption $ sequence ∙ vMD
    end.
  Definition atomic : dom (lib Atom ⇒ m (d (lib (Val L)))) := λ (a:dom (lib Atom)) → _atomic a.

  Definition stepApply : dom (lib Call ⇒ list (string × lib Atom) ⇒ env string L ⇒ m (lib Call)) :=
    λ (c:dom (lib Call)) (xs_args:dom (list (string × lib Atom))) (env:dom (env string L)) →
      let UZ := unzip ∙ xs_args in
      let xs := first ∙ UZ in
      let args := second ∙ UZ in
      ls ← traverse ∙ new (L:=L) ∙ xs ;;
      vDs ← traverse ∙ atomic ∙ args ;;
      putEnv (m:=m) ∙ env ;;
      traverse (t:=list) (m:=m) ∙ (modifyEnv (m:=m) ⊙ uncurry ∙ linsert) $ zip ∙ xs ∙ ls ;;
      traverse (t:=list) (m:=m) ∙ (modifyStore (m:=m) ⊙ uncurry ∙ linsert) $ zip ∙ ls ∙ vDs ;;
      ret (m:=m) ∙ c.

  Definition step : dom (lib Call ⇒ m (lib Call)) := λ (c:dom (lib Call)) →
    match c with
    | IfZC a tc fc =>
        vD ← atomic ∙ a ;;
        v ← promote (m₂:=m) ∙ (vD:dom (d (lib (Val L)))) ;;
        match (v:dom (lib (Val L))) with
        | NumV 0 => ret (m:=m) ∙ (tc:dom (lib Call))
        | NumV _ => ret (m:=m) ∙ (fc:dom (lib Call))
        | NatV => (ret (m:=m) ∙ (tc:dom (lib Call)) m+ ret (m:=m) ∙ (fc:dom (lib Call))) : dom (m (lib Call))
        | _ => mzero
        end
    | LamAppC f a ka =>
        vD ← atomic ∙ f ;;
        v ← promote ∙ vD ;;
        r ← coerceLamCloV ∙ v ;;
        prod_elim4 ∙ r $ λ x k c env →
          stepApply ∙ c ∙ ((x ,, (a:dom (lib Atom))) ∷ (k ,, (ka:dom (lib Atom))) ∷ nil) ∙ env
    | KonAppC k a =>
        vD ← atomic ∙ k ;;
        v ← promote ∙ vD ;;
        r ← coerceKonCloV ∙ v ;;
        prod_elim3 ∙ r $ λ x c env →
          stepApply ∙ c ∙ ((x ,, (a:dom (lib Atom))) ∷ nil) ∙ env
    | HaltC a => ret (m:=m) $ (HaltC a:dom (lib (Call)))
    end.
  
End S.