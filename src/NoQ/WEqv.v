Require Import NoQ.WeakEquivalence.
Require Import NoQ.Relation.
Require Import NoQ.Symmetric.
Require Import NoQ.Transitive.

Class WEqv A :=
  { weqv : relation A
  ; WEqv_WeakEquivalence :> WeakEquivalence weqv
  }.
Arguments weqv {A _} _ _ : simpl never.

Infix "≈" := weqv (at level 70, no associativity).

Definition weak_respectful
{A} `{! WEqv A } (RA:A -> A -> Prop) 
{B} `{! WEqv B } (RB:B -> B -> Prop)
(f:A -> B) (g:A -> B) :=
  forall x y, x ≈ x -> y ≈ y -> RA x y -> RB (f x) (g y).
Arguments weak_respectful {A _} RA {B _} RB f g /.
Infix "-⇉-" := weak_respectful (at level 70, right associativity).

Definition logical_intro_weak
{A B} `{! WEqv A ,! WEqv B } {R1:relation A} {R2:relation B} {f g:A -> B} 
(p:forall x y, proper weqv x -> proper weqv y -> R1 x y -> R2 (f x) (g y)) 
: (R1 -⇉- R2) f g := p.

Ltac logical_intro := (apply logical_intro ; intros) || (apply logical_intro_weak ; intros).
Ltac logical_elim R1 R2 := apply (logical_elim R1 R2).
Ltac logical_weqv :=
  repeat
    match goal with
    (* logical elimination *)
    | [ H : (weqv ⇉ weqv) ?f ?g |- (?f _) ≈ (?g _) ] => apply H
    | [ H : (weqv ⇉ weqv) ?f ?g |- (?g _) ≈ (?f _) ] => apply symmetry ; apply H
    | [ H : ?f ≈ ?g |- (?f _) ≈ (?g _) ] => apply H
    | [ H : ?f ≈ ?g |- (?g _) ≈ (?f _) ] => apply symmetry ; apply H
    | [ H : proper weqv ?f |- proper weqv (?f _) ] => apply H
    | [ H : proper weqv ?f |- (?f _) ≈ (?f _) ] => apply H

    (* terminal *)
    | [ H : ?x ≈ ?y |- ?x ≈ ?y ] => exact H
    | [ H : ?x ≈ ?y |- ?y ≈ ?x ] => apply symmetry ; exact H
    | [ H : ?x ≈ ?y |- ?x ≈ ?x ] => apply (proper_left H)
    | [ H : ?x ≈ ?y |- proper weqv ?x ] => apply (proper_left H)
    | [ H : ?x ≈ ?y |- ?y ≈ ?y ] => apply (proper_right H)
    | [ H : ?x ≈ ?y |- proper weqv ?y ] => apply (proper_right H)
    | [ H : proper ?R ?x |- proper ?R ?x ] => exact H
    | [ H : proper ?R ?x |- ?R ?x ?x ] => exact H
    end.

          
Instance Function_WEqv
{A} `{! WEqv A }
{B} `{! WEqv B }
: WEqv (A -> B) :=
  { weqv := respectful weqv weqv }.
Proof.
  constructor ; constructor ; intros.
  - logical_intro.
    logical_weqv.
  - logical_intro.
    apply (transitivity (y y0)).
    + logical_weqv.
    + logical_weqv.
Defined.