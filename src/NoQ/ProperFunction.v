Inductive ProperFunction A B `{! Eqv A ,! Eqv B } :=
  { ProperFunction_fun : A -> B
  ; ProperFunction_proper : (eqv ⇉ eqv) ProperFunction_fun
  }