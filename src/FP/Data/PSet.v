Require Import FP.Core.
Require Import FP.Data.Prop.
Require Import FP.Classes.Lattice.
Require Import FP.Classes.Monad.

Inductive v_pset A := v_PSet
  { v_unPSet : dom (A ⇒ prop) }.
Arguments v_PSet {A} _.
Arguments v_unPSet {A} _.

Definition pset A := derive (v_pset A) v_unPSet.

Definition PSet {A} : dom ((A ⇒ prop) ⇒ pset A) := λ f →
  v_PSet f : dom (pset A).
Definition unPSet {A} : dom (pset A ⇒ A ⇒ prop) := λ aM →
  v_unPSet (aM : dom (pset A)).

Definition sempty {A} : dom (pset A) := undefined.
Definition suniversal {A} : dom (pset A) := undefined.
Definition ssingleton {A} : dom (A ⇒ pset A) := undefined.
Definition sunion {A} : dom (pset A ⇒ pset A ⇒ pset A) := undefined.
Definition sintersection {A} : dom (pset A ⇒ pset A ⇒ pset A) := undefined.

Definition sinsert {A} : dom (A ⇒ pset A ⇒ pset A) := λ x → sunion ∙ (ssingleton ∙ x).

Instance : forall A, Lattice (pset A).
Admitted.
Definition pset_bind {A B} : dom (pset A ⇒ (A ⇒ pset B) ⇒ pset B) := λ aM k → PSet $ λ b → all $ λ a → 
  imp ∙ (unPSet ∙ aM ∙ a) ∙ (unPSet ∙ (k ∙ a) ∙ b).
  
Instance : Monad pset :=
  { ret := @ssingleton 
  ; bind := @pset_bind 
  }.
Admitted.
Instance : MonadPlus pset :=
  { mzero := @sempty
  ; mplus := @sunion
  }.
Admitted.