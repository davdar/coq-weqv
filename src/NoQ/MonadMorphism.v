Class MonadMorphism (m1 m2:Type -> Type) :=
  { promote : forall {A}, m1 A -> m2 A }.