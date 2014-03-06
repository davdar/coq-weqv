Require Import FP.Core.
Require Import FP.Data.Product.
Require Import FP.Data.Option.
Require Import FP.Classes.Traversable.

Section Vanilla.
  Infix "v∷" := cons (at level 60, right associativity).
  Notation "v[ x , .. , y ]" := (cons x .. (cons y nil) ..).
  
  Definition vlmap {A B} (f:A -> B) : list A -> list B :=
    fix lmap xs :=
      match xs with
      | nil => nil
      | x v∷ xs => f x v∷ lmap xs
      end.

  Inductive vlist_eqv {A} `{! Eqv A } : relation (list A) :=
    | NullListEqv : vlist_eqv nil nil
    | ConsListEqv : forall x y xs ys, x ≃ y -> vlist_eqv xs ys -> vlist_eqv (x v∷ xs) (y v∷ ys).
  Inductive vlist_lte {A} `{! Eqv A ,! Lte A } : relation (list A) :=
    | NullListLte : forall xs, vlist_lte nil xs
    | ConsListLte : forall x y xs ys, x ⊑ y -> vlist_lte xs ys -> vlist_lte (x v∷ xs) (y v∷ ys).
  Global Instance : forall A `{! Eqv A }, Eqv (list A) := { eqv := vlist_eqv }.
  Admitted.
  Global Instance : forall A `{! Eqv A ,! Lte A }, Lte (list A) := { lte := vlist_lte }.
  Admitted.
End Vanilla.

Definition vlist := Coq.Init.Datatypes.list.
Definition vnil {A} : vlist A := Coq.Init.Datatypes.nil.
Definition vcons := Coq.Init.Datatypes.cons.


Definition list (A:qtype) : qtype := {| qdom := vlist (dom A) |}.
Definition nil {A} : dom (list A).
Admitted.
Definition cons {A} : dom (A ⇒ list A ⇒ list A).
Admitted.
Definition list_elim {A B} : dom (list A ⇒ B ⇒ (A ⇒ B ⇒ B) ⇒ B).
Admitted.
Definition linsert {A B} : dom (A ⇒ B ⇒ list (A × B) ⇒ list (A × B)).
Admitted.
Definition llookup {A B} `{! DecEqv (dom A) } : dom (A ⇒ list (A × B) ⇒ qoption B).
Admitted.
Definition zip {A B} : dom (list A ⇒ list B ⇒ list (A × B)).
Admitted.
Definition unzip {A B} : dom (list (A × B) ⇒ list A × list B).
Admitted.
Definition lmap {A B} : dom ((A ⇒ B) ⇒ list A ⇒ list B) := 
  λ (f:dom (A ⇒ B)) (x:dom (list A)) → vlmap (rfun f) x : dom (list B).

Notation "x ∷ xs" := (cons ∙ x ∙ xs) (at level 60, right associativity).

Instance : Traversable list.
Admitted.