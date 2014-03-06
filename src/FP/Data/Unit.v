Require Import FP.Core.

Definition vunit := Coq.Init.Datatypes.unit.
Definition vtt := Coq.Init.Datatypes.tt.
Definition unit := lib vunit.
Definition tt : dom unit := vtt.
