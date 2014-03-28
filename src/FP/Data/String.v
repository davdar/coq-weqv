Require Import FP.Core.
Require Import Coq.Strings.String.

Definition vstring := Coq.Strings.String.string.

Definition string := lib vstring.
Instance : DecEqv (dom string).
Admitted.