Class Functor (t:Type -> Type) :=
  { fmap : forall {A B}, (A -> B) -> t A -> t B }.