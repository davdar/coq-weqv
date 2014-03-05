Require Import FP.Core.
Require Import FP.Data.Product.
Require Import FP.Data.Option.
Require Import FP.Classes.Traversable.

Section Vanilla.
  Infix "v∷" := cons (at level 60, right associativity).
  Notation "v[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Definition lmap {A B} (f:A -> B) : list A -> list B :=
    fix lmap xs :=
      match xs with
      | nil => nil
      | x v∷ xs => f x v∷ lmap xs
      end.

  Inductive list_eqv {A} `{! Eqv A } : relation (list A) :=
    | NullListEqv : list_eqv nil nil
    | ConsListEqv : forall x y xs ys, x ≃ y -> list_eqv xs ys -> list_eqv (x v∷ xs) (y v∷ ys).
  Inductive list_lte {A} `{! Eqv A ,! Lte A } : relation (list A) :=
    | NullListLte : forall xs, list_lte nil xs
    | ConsListLte : forall x y xs ys, x ⊑ y -> list_lte xs ys -> list_lte (x v∷ xs) (y v∷ ys).
  Global Instance : forall A `{! Eqv A }, Eqv (list A) := { eqv := list_eqv }.
  Admitted.
  Global Instance : forall A `{! Eqv A ,! Lte A }, Lte (list A) := { lte := list_lte }.
  Admitted.
End Vanilla.

Definition qlist (A:qtype) : qtype := {| qdom := list (dom A) |}.
Definition qnil {A} : dom (qlist A).
Admitted.
Definition qcons {A} : dom (A ⇒ qlist A ⇒ qlist A).
Admitted.
Definition qlist_elim {A B} : dom (qlist A ⇒ B ⇒ (A ⇒ B ⇒ B) ⇒ B).
Admitted.
Definition qinsert {A B} : dom (A ⇒ B ⇒ qlist (A × B) ⇒ qlist (A × B)).
Admitted.
Definition qlookup {A B} `{! DecEqv (dom A) } : dom (A ⇒ qlist (A × B) ⇒ qoption B).
Admitted.
Definition qzip {A B} : dom (qlist A ⇒ qlist B ⇒ qlist (A × B)).
Admitted.
Definition qunzip {A B} : dom (qlist (A × B) ⇒ qlist A × qlist B).
Admitted.
Definition qlmap {A B} : dom ((A ⇒ B) ⇒ qlist A ⇒ qlist B) := 
  λ (f:dom (A ⇒ B)) (x:dom (qlist A)) → lmap (rfun f) x : dom (qlist B).

Notation "x ∷ xs" := (qcons ∙ x ∙ xs) (at level 60, right associativity).

Instance : Traversable qlist.
Admitted.