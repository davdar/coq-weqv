Require Import FP.Core.
Require Import FP.Data.Unit.
Require Import FP.Classes.Lattice.

Definition vbool := Coq.Init.Datatypes.bool.
Definition vtrue := Coq.Init.Datatypes.true.
Definition vfalse := Coq.Init.Datatypes.false.

Definition bool := lib bool.
Definition true : dom bool := vtrue.
Definition false : dom bool := vfalse.
Definition case {A} : dom (bool ⇒ (unit ⇒ A) ⇒ (unit ⇒ A) ⇒ A) := λ b t f →
  if b : dom bool then t ∙ tt else f ∙ tt.
Global Opaque true.
Global Opaque false.
Global Opaque case.
Ltac bool_induction e :=
  induction e ;
  repeat
    match goal with
    | |- context[Coq.Init.Datatypes.true] => change Coq.Init.Datatypes.true with true
    | |- context[Coq.Init.Datatypes.false] => change Coq.Init.Datatypes.false with false
    end.
  
Definition and : dom (bool ⇒ bool ⇒ bool) := λ x y → case ∙ x ∙ (λ _ → y) ∙ (λ _ → false).

Definition bool_beta_true {A} t f : case (A:=A) ∙ true ∙ t ∙ f ≃ t ∙ tt := libReflexivity.
Definition bool_beta_false {A} t f : case (A:=A) ∙ false ∙ t ∙ f ≃ f ∙ tt := libReflexivity.
Ltac BoolRewrite :=
  match goal with
  | |- ⟨ case ∙ true ∙ ?t ∙ ?f IN _ |_| _ ⟩ => ReplaceBy (bool_beta_true t f)
  | |- ⟨ case ∙ false ∙ ?t ∙ ?f IN _ |_| _ ⟩ => ReplaceBy (bool_beta_false t f)
  end.
Definition bool_eta e : case ∙ e ∙ (λ _ → true) ∙ (λ _ → false) ≃ e.
Proof.
  bool_induction e ; Re fail || BoolRewrite.
Qed.

Definition bool_beta_lte {A} `{! Lattice A } e t f : case (A:=A) ∙ e ∙ t ∙ f ⊑ t ∙ tt ⊔ f ∙ tt.
Proof.
  bool_induction e ; Re fail || BoolRewrite ; apply join_left || apply join_right.
Qed.