Definition relation (A:Type) := A -> A -> Prop.

Definition respectful
{A} (RA:A -> A -> Prop) 
{B} (RB:B -> B -> Prop)
(f:A -> B) (g:A -> B) :=
  forall x y, RA x y -> RB (f x) (g y).
Infix "⇉" := respectful (at level 70, right associativity).

(*
Definition logical_intro
{A B} {R1:relation A} {R2:relation B} 
{t} `{! Logical A B (t A B) } 
{f g:t A B} 
(p:forall x y, R1 x y -> R2 (f ⊙ x) (g ⊙ y)) 
: (R1 ⇉ R2) f g := p.

Definition logical_elim
{A B} (R1:relation A) (R2:relation B) 
{t} `{! Logical A B (t A B) } 
{f g:t A B} {x y:A}
(p1:R1 x y) (p2:(R1 ⇉ R2) f g) : R2 (f ⊙ x) (g ⊙ y) := p2 _ _ p1.
*)
          
Definition proper {A} (R:A -> A -> Prop) (x:A) := R x x.