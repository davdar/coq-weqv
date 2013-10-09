Definition relation (A:Type) := A -> A -> Type.

Definition proper {A} (R:relation A) (x:A) := R x x.

Definition respectful {A B} (RA:relation A) (RB:relation B) : relation (A -> B) :=
  fun f g => forall x y, RA x y -> RB (f x) (g y).

Module Notation.
  Infix "==>" := respectful (right associativity, at level 100).
End Notation.