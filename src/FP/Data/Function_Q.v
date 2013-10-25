Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Function.
Require Import FP.Data.Relation.
Require Import FP.Classes.Eqv.
Require Import FP.Data.Function.
Require Import FP.Classes.WeakEqv.
Require Import FP.Classes.Reflexive.

Import WeakSetoid.Notation.
Import Eqv.Notation.
Import WeakEqv.Notation.
Import Function.Notation.

(*
  -- what I want the goal for compose_Q to actually look like...
  refine(
    let rawf := fun (g:DD (B ⇨ C)) (f:DD (A ⇨ B)) (x:DD A) => g ⊛ (f ⊛ x) in
    let pf1 : forall g f, proper weqv (fun x => rawf g f x) := _ in
    let pf2 : forall g, proper weqv (fun f => (mk_DD_f (fun x => rawf g f x) (pf1 g f))) := _ in
    mk_DD_f (fun g => mk_DD_f (fun f => mk_DD_f (fun x => rawf g f x) (pf1 g f)) (pf2 g)) _
             ) ; abstract (intros ; repeat (unfold rawf ; decide_weqv)).
*)

Definition id_Q {A:WeakSetoid} : DD (A ⇨ A) := λ x → x.
Definition id_Q_beta {A:WeakSetoid} (x:DD A) : id_Q ⊛ x ≃ x := DD_proper x.
Definition compose_Q {A B C:WeakSetoid} : DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C)) := λ g f x → g ⊛ (f ⊛ x).
Definition compose_Q_beta {A B C:WeakSetoid} (g:DD (B ⇨ C)) (f:DD (A ⇨ B)) (x:DD A) : compose_Q ⊛ g ⊛ f ⊛ x ≃ g ⊛ (f ⊛ x) :=
  reflexivity.
Definition apply_Q {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ A ⇨ B) := λ f x → f ⊛ x.
Definition apply_Q_beta {A B:WeakSetoid} (f:DD (A ⇨ B)) (x:DD A) : apply_Q ⊛ f ⊛ x ≃ f ⊛ x :=
  reflexivity.
Definition flip_Q {A B C:WeakSetoid} : DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) := λ f y x → f ⊛ x ⊛ y.
Definition flip_Q_beta {A B C:WeakSetoid} (f:DD (A ⇨ B ⇨ C)) (y:DD B) (x:DD A) : flip_Q ⊛ f ⊛ y ⊛ x ≃ f ⊛ x ⊛ y :=
  reflexivity.
Definition apply_to_Q {A B:WeakSetoid} : DD (A ⇨ (A ⇨ B) ⇨ B) := flip_Q ⊛ apply_Q.
Definition apply_to_Q_beta {A B:WeakSetoid} (x:DD A) (f:DD (A ⇨ B)) : apply_to_Q ⊛ x ⊛ f ≃ f ⊛ x :=
  reflexivity.