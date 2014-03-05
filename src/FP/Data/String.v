Require Export Coq.Strings.String.
Require Import FP.Core.

Definition qstring := lib string.
Instance : DecEqv (dom qstring).
Admitted.