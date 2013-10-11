Inductive Sum (A B:Type) : Type :=
  | ι₁ : A -> Sum A B
  | ι₂ : B -> Sum A B.