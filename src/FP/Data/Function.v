Require Import FP.Core.

Definition Function A B := A -> B.

Definition vapply {A B} (f:A -> B) (x:A) : B := f x.
Arguments vapply {A B} f x /.

Definition vcompose {A B C} (g:B -> C) (f:A -> B) (x:A) : C := g (f x).
Arguments vcompose {A B C} g f x /.