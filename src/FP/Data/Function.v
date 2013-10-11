Definition id {A:Type} (x:A) : A := x.
Arguments id {A} x / .
Definition apply {A B:Type} : (A -> B) -> A -> B := id.
Arguments apply {A B} / _ _.
Definition flip {A B C:Type} (f:A -> B -> C) (y:B) (x:A) := f x y.
Arguments flip {A B C} f y x /.
Definition compose {A B C:Type} (g:B -> C) (f:A -> B) (x:A) : C := g (f x).
Arguments compose {A B C} g f x /.
Definition compose12 {A B C D:Type} : (C -> D) -> (A -> B -> C) -> A -> B -> D := compose compose compose.

Module Notation.
  Notation "'begin' e1 'end'" := ((e1)) (at level 0, only parsing).
  Notation "f $ x" := (f x) (at level 89, right associativity, only parsing).
  Notation "x ` f ` y" := (f x y) (at level 88, f at next level, right associativity, only parsing).

  Infix "∙" := compose (at level 65, right associativity).
  Infix "∙∶" := compose12 (at level 65, right associativity).
  Notation "A → B" := (A -> B) (at level 90, right associativity).
  (*
  Notation "∀ x : A , B" := 
    (forall x : A , B) 
    (at level 200, right associativity, x ident).
  Notation "∀ x .. y , P" := 
    (forall x, .. (forall y, P) ..)
    (at level 200, right associativity, x binder, y binder).
  Notation "∃ x : A , B" :=
    (exists x : A, B)
    (at level 200, right associativity, x ident).
  Notation "∃ x .. y , P" :=
    (exists x, .. (exists y, P) ..)
    (at level 200, right associativity, x binder, y binder).
  *)
  (*
  Print Grammar constr.
  *)
End Notation.