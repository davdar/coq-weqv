Require Import NoQ.Universe.
Require Import NoQ.Eqv.
Require Import NoQ.LibReflexive.
Require Import NoQ.Symmetric.
Require Import NoQ.Relation.
Require Import NoQ.Reflexive.
Require Import NoQ.Type.
Require Import NoQ.Function.
Require Import NoQ.PreOrder.

Class Arrow (t:UPO -> UPO -> UPO) :=
  { lambda_p : forall {A B:UPO}, (dom A -> dom B) -> Type
  ; lambda : forall {A B:UPO} (f:dom A -> dom B), lambda_p f -> dom (t A B)
  ; apply : forall {A B:UPO}, dom (t A B) -> dom A -> dom B 
  ; id : forall {A:UPO}, dom (t A A)
  ; compose : forall {A B C:UPO}, dom (t (t B C) (t (t A B) (t A C)))
  (* computation *)
  ; id_apply : 
      forall {A:UPO} (x:dom A),
      apply id x ≃ x
  ; compose_apply : 
      forall {A B C:UPO} (g:dom (t B C)) (f:dom (t A B)) (x:dom A),
      apply (apply (apply compose g) f) x ≃ apply g (apply f x)
  (* laws *)
  ; compose_id_left : 
      forall {A B:UPO} (f:dom (t A B)),
      apply (apply compose id) f ≃ f
  ; compose_id_right : 
      forall {A B:UPO} (f:dom (t A B)),
      apply (apply compose f) id ≃ f
  ; compose_associativity :
      forall {A B C D:UPO} (h:dom (t C D)) (g:dom (t B C)) (f:dom (t A B)),
      apply (apply compose (apply (apply compose h) g)) f ≃ apply (apply compose h) (apply (apply compose g) f)
  }.
Arguments id {t Arrow A} : simpl never.
Arguments apply {t Arrow A B} _ _ : simpl never.
Arguments compose {t Arrow A B C} : simpl never.
Infix "∙" := apply (at level 20, left associativity).
Notation "g ∙⊙∙ f" := (compose ∙ g ∙ f) (at level 90, right associativity).
Notation "'λ' x .. y → e" := 
  (lambda (fun x => .. (lambda (fun y => e) _) ..) _) 
  (x binder, y binder, at level 100, left associativity).

Definition lrespectful
{t} `{! Arrow t }
{A B:UPO}
(RA:dom A -> dom A -> Prop)
(RB:dom B -> dom B -> Prop)
(f g:dom (t A B)) := forall x y, RA x y -> RB (f ∙ x) (g ∙ y).
Infix "∙⇉∙" := lrespectful (at level 70, right associativity).

Class Logical t `{! Arrow t } :=
  { logical_intro : 
      forall {A B:UPO} (f g:dom (t A B)), 
      f ≃ g -> (eqv ∙⇉∙ eqv) f g
  ; logical_elim : 
      forall {A B:UPO} (f g:dom (t A B)), 
      (eqv ∙⇉∙ eqv) f g -> eqv f g 
  }.

Definition logical_intro' :
forall 
  {t} `{! Arrow t ,! Logical t }
  {A B:UPO} (f g:dom (t A B)), 
f ≃ g -> forall (x y:dom A), x ≃ y -> f ∙ x ≃ g ∙ y := @logical_intro.

Ltac logical :=
repeat
  match goal with
  | |- ?x ∙ _ ≃ ?y ∙ _ => apply (logical_intro x y)
  | |- _ ≃ _ => solve [auto || apply lib_reflexivity || (apply symmetry ; auto)]
  end.

Class Monotonic t `{! Arrow t } :=
  { monotonic_intro : 
      forall {A B:UPO} (f g:dom (t A B)), 
      f ⊑ g -> (lte ∙⇉∙ lte) f g
  ; monotonic_elim : 
      forall {A B:UPO} (f g:dom (t A B)), 
      (lte ∙⇉∙ lte) f g -> f ⊑ g 
  }.

Ltac monotonic :=
repeat
  match goal with
  | |- ?x ∙ _ ⊑ ?y ∙ _ => apply (monotonic_intro x y)
  | |- _ ⊑ _ => solve [(apply reflexivity ; apply lib_reflexivity) || auto]
  end.

Ltac decide_upo := 
  repeat
  match goal with
  | [ |- lambda_p _ ] => unfold lambda_p ; simpl
  | [ |- _ /\ _ ] => split
  | [ |- proper (eqv ⇉ eqv) _ ] => unfold proper,"⇉" ; intros ; logical
  | [ |- proper (lte ⇉ lte) _ ] => unfold proper,"⇉" ; intros ; monotonic
  end.