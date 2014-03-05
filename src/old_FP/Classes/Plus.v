Class Plus (T:Type) : Type := { plus : T -> T -> T }.

Module Notation.
  Infix "⊕" := plus (right associativity, at level 60).
End Notation.