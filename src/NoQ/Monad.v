Require Import NoQ.List.
Require Import NoQ.Relation.
Require Import NoQ.Function.
Require Import NoQ.Universe.
Require Import NoQ.Eqv.
Require Import NoQ.PreOrder.
Require Import NoQ.MArrow.
Require Import NoQ.Arrow.

Class Monad (m:UPO -> UPO) :=
  { ret : forall {A}, dom (A ⇗ m A)
  ; extend : forall {A B}, dom (A ⇗ m B) -> dom (m A ⇗ m B)
  ; extend_ret : forall {A}, extend (ret:dom (A ⇗ m A)) ≃ id
  ; extend_after_ret : forall {A B} (k:dom (A ⇗ m B)) , (extend k ∙⊙∙ ret) ≃ k
  ; extend_extend : forall {A B C} (g:dom (B ⇗ m C)) (f:dom (A ⇗ m B)),
       (extend g ∙⊙∙ extend f) ≃ extend (extend g ∙⊙∙ f)
  }.

Notation "aM >>= k" := (extend k ∙ aM) (at level 50, left associativity).
Notation "k =<< aM" := (extend k ∙ aM) (at level 60, right associativity).
Notation "x <- c1 ;; c2" := (extend (lambda (fun x => c2)) c1)
  (at level 100, c1 at next level, right associativity).

Section Monad.
  Context {m:UPO -> UPO} `{! Monad m }.
  
  Definition seq {A B} (xM:dom (m A)) (yM:dom (m B)) : dom (m B). refine(
    xM >>= λ _ → yM
  ).
  Proof.
    decide_upo.
  Defined.

  Definition list_mapM {A B} (f:dom (A ⇗ m B)) : dom (slist A ⇗ m (slist B)). := fix self (xs:list A) : m (list B) :=
      match xs with
      | [] => ret []
      | x::xs =>
          y <- f x ;;
          ys <- self xs ;;
          ret $ y::ys
      end.
  
  Definition monad_map {A B} (f:A -> B) (xM:m A) : m B :=
    x <- xM ;;
    ret $ f x.
End Monad.

Infix ">>" := seq (at level 50, left associativity).
Notation "e1 ;; e2" := (seq e1 e2)
  (at level 100, right associativity).
