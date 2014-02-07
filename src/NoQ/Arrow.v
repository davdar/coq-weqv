Require Import NoQ.Universe.
Require Import NoQ.Eqv.
Require Import NoQ.LibReflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.Type.
Require Import NoQ.Function.

Class Arrow U `{! Universe U ,! UHasEqv U } (arrow:U -> U -> U) :=
  { apply : forall {A B:U}, dom (arrow A B) -> dom A -> dom B 
  ; id : forall {A:U}, dom (arrow A A)
  ; compose : forall {A B C:U}, dom (arrow B C) -> dom (arrow A B) -> dom (arrow A C)
  (* computation *)
  ; id_apply : 
      forall {A:U} (x:dom A),
      apply id x ≃ x
  ; compose_apply : 
      forall {A B C:U} (g:dom (arrow B C)) (f:dom (arrow A B)) (x:dom A),
      apply (compose g f) x ≃ apply g (apply f x)
  (* laws *)
  ; compose_id_left : 
      forall {A B:U} (f:dom (arrow A B)),
      compose id f ≃ f
  ; compose_id_right : 
      forall {A B:U} (f:dom (arrow A B)),
      compose f id ≃ f
  ; compose_associativity :
      forall {A B C D:U} (h:dom (arrow C D)) (g:dom (arrow B C)) (f:dom (arrow A B)),
      compose (compose h g) f ≃ compose h (compose g f)
  }.
Arguments apply {U _ _ _ _ A B} _ _ : simpl never.
Arguments compose {U _ _ _ _ A B C} _ _ : simpl never.
Infix "∙" := apply (at level 20, left associativity).
Infix "∙⊙∙" := compose (at level 90, right associativity).

Definition lrespectful
{U t} `{! Universe U ,! UHasEqv U ,! Arrow U t }
{A B:U}
(RA:dom A -> dom A -> Prop)
(RB:dom B -> dom B -> Prop)
(f g:dom (t A B)) := forall x y, RA x y -> RB (f ∙ x) (g ∙ y).
Infix "∙⇉∙" := lrespectful (at level 70, right associativity).

Class Logical {U} t `{! Universe U ,! UHasEqv U ,! Arrow U t } :=
  { logical_intro : 
      forall {A B:U} (f g:dom (t A B)), 
      f ≃ g -> (eqv ∙⇉∙ eqv) f g
  ; logical_elim : 
      forall {A B:U} (f g:dom (t A B)), 
      (eqv ∙⇉∙ eqv) f g -> eqv f g 
  }.

Definition logical_intro' :
forall 
  {U t} `{! Universe U ,! UHasEqv U ,! Arrow U t ,! Logical t }
  {A B:U} (f g:dom (t A B)), 
f ≃ g -> forall (x y:dom A), x ≃ y -> f ∙ x ≃ g ∙ y := @logical_intro.

Ltac logical :=
repeat
  match goal with
  | |- ?x ∙ _ ≃ ?y ∙ _ => apply (logical_intro x y)
  | |- _ ≃ _ => solve [auto || apply lib_reflexivity || (apply symmetry ; auto)]
  end.

Instance Function_Arrow : Arrow Type Function :=
  { apply A B f x := f x 
  ; id A x := x
  ; compose A B C f g x := f (g x)
  }.
Proof.
  - intros ; apply lib_reflexivity.
  - intros ; apply lib_reflexivity.
  - intros ; apply lib_reflexivity.
  - intros ; apply lib_reflexivity.
  - intros ; apply lib_reflexivity.
Defined.