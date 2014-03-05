Tactic Notation "chain" tactic(t1) "|+|" tactic(t2) := ((t1 ; try t2) || t2).
