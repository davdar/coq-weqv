Class Times (T:Type) : Type := { times : T -> T -> T }.

Module Notation.
  Infix "⊗" := times (right associativity, at level 60).
End Notation.
