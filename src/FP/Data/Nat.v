Require Import FP.Core.

Definition vnat : Type := Coq.Init.Datatypes.nat.
Definition vZ : nat := Coq.Init.Datatypes.O.
Definition vS : nat -> nat := Coq.Init.Datatypes.S.
                   
Definition nat := lib vnat.
Definition Z : dom nat := vZ.
Definition S : dom (nat ⇒ nat) := λ n → (vS:dom nat -> dom nat) n.

Fixpoint _nat_elim {A} (n:dom nat) : dom (A ⇒ (A ⇒ A) ⇒ A) := λ z s →
  match n : dom nat with
  | vZ => z : dom A
  | vS n' => s $ _nat_elim n' ∙ z ∙ s
  end.
Definition nat_elim {A} : dom (nat ⇒ A ⇒ (A ⇒ A) ⇒ A) := λ a → _nat_elim a.
Global Opaque Z.
Global Opaque S.
Global Opaque nat_elim.

Ltac nat_induction e :=
  induction e ;
  repeat
    match goal with
    | H : context [Coq.Init.Datatypes.O] |- _ => change Coq.Init.Datatypes.O with Z in H
    | H : context [Coq.Init.Datatypes.S ?n] |- _ => change (Coq.Init.Datatypes.S n) with (S ∙ n) in H
    | |- context [Coq.Init.Datatypes.O] => change Coq.Init.Datatypes.O with Z
    | |- context [Coq.Init.Datatypes.S ?n] => change (Coq.Init.Datatypes.S n) with (S ∙ n)
    end.

Definition nat_elim_beta_Z {A} z s : nat_elim (A:=A) ∙ Z ∙ z ∙ s ≃ z := libReflexivity.
Definition nat_elim_beta_S {A} z s n : nat_elim (A:=A) ∙ (S ∙ n) ∙ z ∙ s ≃ s ∙ (nat_elim ∙ n ∙ z ∙ s) := libReflexivity.
Ltac NatRewrite :=
  match goal with
  | |- ⟨ nat_elim ∙ Z ∙ ?z ∙ ?s IN _ |_| _ ⟩ => ReplaceBy (nat_elim_beta_Z z s)
  | |- ⟨ nat_elim ∙ (S ∙ ?n) ∙ ?z ∙ ?s IN _ |_| _ ⟩ => ReplaceBy (nat_elim_beta_S z s n)
  end.

Definition pred : dom (nat ⇒ nat) := λ n →
  nat_elim ∙ n ∙ Z ∙ id.