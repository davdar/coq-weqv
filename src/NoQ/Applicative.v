Class Applicative (t:Type -> Type) :=
  { fret : forall {A}, A -> t A
  ; fapply : forall {A B}, t (A -> B) -> t A -> t B
  }.

Infix "<@>" := fapply (left associativity, at level 50).