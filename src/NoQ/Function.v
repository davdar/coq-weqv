Notation "f $ x" := (f x) (at level 89, right associativity, only parsing).
Definition compose {A B C} (g:B -> C) (f:A -> B) (x:A) : C := g (f x).
Infix "⊙" := compose (right associativity, at level 60).
Arguments compose {A B C} g f x /.

Definition uncurry {A B C} (f:A -> B -> C) (xy:A*B) : C :=
  let (x,y) := xy in f x y.

Definition Function (A:Type) (B:Type) := A -> B.
