Class Multiplicative (T:Type) : Type := { mult : T -> T -> T }.

Module Notation.
  Infix "⊗" := mult (right associativity, at level 60).
End Notation.
