Inductive Product (A B:Type) : Type := mk_Product
  { π₁ : A
  ; π₂ : B
  }.

Inductive DProduct (A:Type) (B:A -> Type) : Type := mk_DProduct
  { dπ₁ : A
  ; dπ₂ : B dπ₁
  }.