Require Import AAI.Monads.Classes.Env.
Require Import AAI.Monads.Classes.Store.
Require Import AAI.Monads.Classes.Time.
Require Import AAI.Monads.Classes.Transition.
Require Import AAI.Notation.
Require Import Coq.Strings.String.
Require Import NoQ.Applicative.
Require Import NoQ.DecEq.
Require Import NoQ.Function.
Require Import NoQ.Functor.
Require Import NoQ.List.
Require Import NoQ.ListInstances.
Require Import NoQ.Monad.
Require Import NoQ.MonadMorphism.
Require Import NoQ.MonadPlus.
Require Import NoQ.Option.
Require Import NoQ.Pointed.
Require Import NoQ.String.
Require Import NoQ.Traversable.

Inductive Op := Add1 | Sub1.

Inductive Call :=
  | IfZC (a:Atom) (tc:Call) (fc:Call)
  | LamAppC (f:Atom) (x:Atom) (k:Atom)
  | KonAppC (k:Atom) (x:Atom)
  | HaltC (a:Atom)
with Atom :=
  | LitA (n:nat)
  | VarA (x:string)
  | LamA (x:string) (k:string) (c:Call)
  | KonA (x:string) (c:Call)
  | PrimA (o:Op) (args:list Atom).

Inductive Val L :=
  | NumV (n:nat)
  | NatV
  | LamCloV (x:string) (k:string) (c:Call) (env:Env string L)
  | KonCloV (x:string) (c:Call) (env:Env string L).
Arguments NumV {L} n.
Arguments NatV {L}.
Arguments LamCloV {L} x k c env.
Arguments KonCloV {L} x c env.

(* Variable names and their meanings:
   - m : the interpretation monad 
   - d : the domain of the state space
   - L : locations
   - T : time 
*)
Class Analysis (d:Type -> Type) (L:Type) (T:Type) (m:Type -> Type) :=
  { Analysis_d_Monad           :> Monad d
  ; Analysis_d_Traversable     :> Traversable d
  ; Analysis_L_DecEq           :> DecEq L
  ; Analysis_T_Addressable     :> Addressable L string T
  ; Analysis_m_Monad           :> Monad m
  ; Analysis_m_MonadPlus       :> MonadPlus m
  ; Analysis_m_MonadMorphism   :> MonadMorphism d m
  ; Analysis_m_MonadEnvState   :> MonadEnvState string L m
  ; Analysis_m_MonadStoreState :> MonadStoreState d L (Val L) m
  ; Analysis_m_MonadTimeState  :> MonadTimeState T m
  }.
 
Section S.
  Context {d L T m} `{! Analysis d L T m }.
  Context (delt:Op -> list (Val L) -> option (Val L)). 
  
  Definition coerceLamCloV (x:Val L) : m (string × string × Call × Env string L) :=
    match x with
    | LamCloV x k c env => ret (x, k, c, env)
    | _ => mzero
    end.
  Definition coerceKonCloV (x:Val L) : m (string × Call × Env string L) :=
    match x with
    | KonCloV x c env => ret (x, c, env)
    | _ => mzero
    end.

  Fixpoint atomic (a:Atom) : m (d (Val L)) :=
    match a with
    | LitA n => ret $ ret $ NumV n
    | VarA x =>
        a <- lookupEnv x ;;
        lookupStore a
    | LamA x k c =>
        env <- getEnv ;;
        ret $ ret $ LamCloV x k c env
    | KonA x c =>
        env <- getEnv ;;
        ret $ ret $ KonCloV x c env
    | PrimA o args =>
        vDs <- list_mapM atomic args ;;
        let vsD : d (list (Val L)) := tsequence vDs in
        let vMD : d (option (Val L)) := monad_map (delt o) vsD in
        mplusFromOption $ tsequence vMD
    end.

  Definition stepApply (c:Call) (xs_args:list (string × Atom)) (env:Env string L) : m Call :=
    let '(xs, args) := unzip xs_args in
    ls <- list_mapM alloc xs ;;
    vDs <- list_mapM atomic args ;;
    putEnv env ;;
    list_mapM (modifyEnv ∙ uncurry insert) $ zip xs ls ;;
    list_mapM (modifyStore ∙ uncurry insert) $ zip ls vDs ;;
    ret c.

  Definition step (c:Call) : m Call :=
    match c with
    | IfZC a tc fc =>
        v <- promote =<< atomic a ;;
        match v with
        | NumV 0 => ret tc
        | NumV _ => ret fc
        | NatV => ret tc <|> ret fc
        | _ => mzero
        end
    | LamAppC f a ka =>
        r <- coerceLamCloV =<< promote =<< atomic f ;; 
        let '(x, k, c, env) := r in
        stepApply c [(x, a); (k, ka)] env
    | KonAppC k a =>
        r <- coerceKonCloV =<< promote =<< atomic k ;;
        let '(x, c, env) := r in
        stepApply c [(x, a)] env
    | HaltC a => ret $ HaltC a
    end.
  
End S.

Parameter monad_refine : 
  forall (m1:Type -> Type) (m2:Type -> Type) `{! Monad m1 ,! Monad m2 },
  Prop.
Infix "⊏" := monad_refine (at level 70, no associativity).

Parameter galois_refine :
  forall {A B}, (A -> A) -> (B -> B) -> Prop.
Infix "≤" := galois_refine (at level 70, no associativity).

Section Thm.
  Context {d_con L_con T_con m_con} `{! Analysis d_con L_con T_con m_con }.
  Context (delt_con:Op -> list (Val L_con) -> option (Val L_con)). 
  Context {ss_con} `{! Transition ss_con m_con }.

  Context {d_abs L_abs T_abs m_abs} `{! Analysis d_abs L_abs T_abs m_abs }.
  Context (delt_abs:Op -> list (Val L_abs) -> option (Val L_abs)). 
  Context {ss_abs} `{! Transition ss_abs m_abs }.

  Context (mrefine:m_con ⊏ m_abs).
  
  Definition thm : transition (step delt_con) ≤ transition (step delt_abs).
  Admitted.
End Thm.