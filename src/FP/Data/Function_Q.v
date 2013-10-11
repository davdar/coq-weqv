Require Import FP.Data.WeakSetoid.
Require Import FP.Data.Function.
Require Import FP.Classes.Eqv.
Require Import FP.Data.RewriteState.

Import WeakSetoid.Notation.
Import Eqv.Notation.

Definition id_Q {A:WeakSetoid} : DD (A ⇨ A) := 
  mk_DD (A ⇨ A) id (fun _ _ => id).
Definition id_Q_beta {A:WeakSetoid} (x:DD A) : id_Q ⊛ x ≃ x.
Proof.
  decide_weqv.
Defined.
Ltac R_id_Q_beta :=
  match goal with
  | [ |- RewriteState (id_Q ⊛ ?x) _ _ ] => ReplaceBy (id_Q_beta x)
  end.

Definition compose_Q {A B C:WeakSetoid} : DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C)) :=
  mk_DD ((B ⇨ C) ⇨ (A ⇨ B) ⇨ A ⇨ C) 
        compose
        (fun _ _ Rff' g g' Rgg' x x' Rxx' => Rff' (g x) (g' x') (Rgg' x x' Rxx')).
Definition compose_Q_beta 
  {A B C:WeakSetoid} (g:DD (B ⇨ C)) (f:DD (A ⇨ B)) (x:DD A) 
  : compose_Q ⊛ g ⊛ f ⊛ x ≃ g ⊛ (f ⊛ x).
Proof.
  decide_weqv.
Defined.
Ltac R_compose_Q_beta :=
  match goal with
  | [ |- RewriteState (compose_Q ⊛ ?g ⊛ ?f ⊛ ?x) _ _ ] => ReplaceBy (compose_Q_beta g f x)
  end.

Definition apply_Q {A B:WeakSetoid} : DD ((A ⇨ B) ⇨ A ⇨ B) :=
  mk_DD ((A ⇨ B) ⇨ A ⇨ B)
        apply
        (fun _ _ Rfg x y Rxy => Rfg x y Rxy).

Definition flip_Q {A B C:WeakSetoid} : DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C) :=
    mk_DD ((A ⇨ B ⇨ C) ⇨ B ⇨ A ⇨ C)
          flip
          (fun _ _ Rfg y y' Ryy' x x' Rxx' => Rfg x x' Rxx' y y' Ryy').

Definition apply_to_Q {A B:WeakSetoid} : DD (A ⇨ (A ⇨ B) ⇨ B) := flip_Q ⊛ apply_Q.

Ltac R_Function_beta := R_id_Q_beta || R_compose_Q_beta.