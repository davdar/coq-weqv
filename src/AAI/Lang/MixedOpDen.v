(*

Playing around with mixed operational denotational.  Not sure this is
helpful at all...

Inductive Command dom T L : Type -> Type :=
  | Return : forall {A}, A -> Command dom T L A
  | Bind : forall {A B}, Command dom T L A -> (A -> Command dom T L B) -> Command dom T L B
  (*
  | Delay : Call -> Command dom T L (Val L)
  *)
  | ModifyEnv : 
      forall {A}, (Env string L -> Command dom T L (A × Env string L)) -> Command dom T L A
  | ModifyStore : 
      forall {A}, (Store dom L (Val L) -> Command dom T L (A × Store dom L (Val L))) -> Command dom T L A
  | ModifyTime : 
      forall {A}, (T -> Command dom T L (A × T)) -> Command dom T L A.
Arguments Return {dom T L A} _.

Instance : forall {dom T L}, Monad (Command dom T L) :=
  { ret := @Return dom T L
  ; bind := @Bind dom T L
  }.

Section I.
  Context {var:Type}.
  Context {T:Type}.
  Context {L:Type}.
  Context {dom} `{! Functor dom ,! Pointed dom }.
  Context (delt:Op -> list (Val L) -> option (Val L)). 

  Fixpoint atomic (a:Atom) : Command dom T L (dom (Val L)) :=
    match a with
    | LitA n => ret $ point $ NumV n
    | VarA x =>
        a <- lookupEnv x ;;
        lookupStore a
    | LamA x k c =>
        env <- getEnv ;;
        ret $ fret $ LamCloV x k c env
    | KonA x c =>
        env <- getEnv ;;
        ret $ fret $ KonCloV x c env
    | PrimA o args =>
        vDs <- mapM atomic args ;;
        let vsD : dom (list (Val L)) := tsequence vDs in
        let vMD : dom (option (Val L)) := fmap (delt o) vsD in
        mplusFromOption $ tsequence vMD
    end.
End I.
*)