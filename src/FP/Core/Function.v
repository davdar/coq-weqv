Require Import FP.Core.Notation.

Notation "f v$ x" := (f x) (only parsing).
Notation "x v` f ` y" := (f x y) (only parsing).

Definition von {A B C} (o:B -> B -> C) (f:A -> B) (x y:A) : C := o (f x) (f y).