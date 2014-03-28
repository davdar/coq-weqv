Require Import FP.Core.
Require Import FP.Data.List.
Require Import FP.Data.Product.
Require Import FP.Classes.Lattice.
Require Import FP.Classes.Monad.

Inductive member {A:qtype} : dom A -> dom (list A) -> Prop :=
  | HeadMember : forall x y xs, x ≃ y -> member y (x∷xs)
  | TailMember : forall x x' xs, member x xs -> member x (x'∷xs).
Infix "∈" := member.
Notation "x ∉ xs" := (not (x ∈ xs)).

Inductive subset {A:qtype} : relation (dom (list A)) :=
  | NullPermutation : forall ys, subset nil ys
  | ConsPermutation : forall x xs ys, x ∈ ys -> subset xs ys -> subset (x∷xs) ys.
Infix "⊆" := subset (at level 50, no associativity).

Inductive unique {A:qtype} : dom (list A) -> Prop :=
  | NullUnique : unique nil
  | ConsUnique : forall x xs, x ∉ xs -> unique xs -> unique (x∷xs).

Definition equiv {A} (xs ys:dom (list A)) := xs ⊆ ys /\ ys ⊆ xs.

Inductive v_listSet A := v_ListSet 
  { v_listSetData : dom (list A) 
  ; v_listSetUnique : unique v_listSetData
  }.
Arguments v_ListSet {A} _ _.
Arguments v_listSetData {A} _.
Arguments v_listSetUnique {A} _.

Instance : forall A, Eqv (dom A) -> Eqv (v_listSet A) :=
  { eqv xs ys := equiv (v_listSetData xs) (v_listSetData ys) }.
Admitted.

Instance : forall A, Lte (dom A) -> Lte (v_listSet A) :=
  { lte xs ys := subset (v_listSetData xs) (v_listSetData ys) }.
Admitted.

Definition listSet (A:qtype) : qtype := {| qdom := v_listSet A |}.

Definition sempty {A} : dom (listSet A) := undefined.
Definition sinsert {A} : dom (A ⇒ listSet A ⇒ listSet A) := undefined.
Definition siter {A B} : dom (listSet A ⇒ (A ⇒ B) ⇒ (B ⇒ B ⇒ B) ⇒ B) := undefined.
Definition sjoins {A B} `{! Lattice B } : dom (listSet A ⇒ (A ⇒ B) ⇒ B) := λ xs f →
  siter ∙ xs ∙ f ∙ join.
Definition ssingleton {A} : dom (A ⇒ listSet A) := λ x → sinsert ∙ x ∙ sempty.

Instance : forall A, Lattice (listSet A).
Admitted.
Instance : Monad listSet.
Admitted.
Instance : MonadPlus listSet.
Admitted.