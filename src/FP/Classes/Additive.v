Class Additive {T:Type} : Type := { add : T -> T -> T }.

Module Notation.
  Infix "⊕" := add (right associativity, at level 60).
End Notation.
