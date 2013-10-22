Tactic Notation "chain" tactic(t1) "|+|" tactic(t2) := ((t1 ; try t2) || t2).

Ltac unfold_in_term name X :=
  let X' := eval cbv beta delta[name] in X in
  change X with X'.


