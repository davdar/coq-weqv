Definition implies (A:Prop) (B:Prop) : Prop := A -> B.
Arguments implies A B /.

Infix "∧" := (and : Prop -> Prop -> Prop) (left associativity, at level 40).
