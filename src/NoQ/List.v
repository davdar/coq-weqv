Require Import NoQ.DecEq.
Require Import NoQ.PreOrder.

Arguments nil {A}.
Notation "[ ]" := nil.
Arguments cons {A} _ _.
Infix "::" := cons.
Arguments app {A} _ _.
Infix "++" := app.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Fixpoint zip {A B} (xs:list A) (ys:list B) : list (A * B) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x,y)::zip xs ys
  end.

Fixpoint unzip {A B} (xys:list (A*B)) : list A * list B :=
  match xys with
  | [] => ([], [])
  | (x,y)::xys =>
      let (xs, ys) := unzip xys in (x::xs, y::ys)
  end.

Fixpoint lookup {A B} `{! DecEq A } (x:A) (xys:list (A*B)) : option B :=
  match xys with
  | [] => None
  | (x',y)::xys => if x == x' then Some y else lookup x xys
  end.

Fixpoint remove {A B} `{! DecEq A } (x:A) (xys:list (A*B)) : list (A*B) :=
  match xys with
  | [] => []
  | (x',y)::xys => if x == x' then remove x xys else (x',y)::remove x xys
  end.

Definition insert {A B} `{! DecEq A } (x:A) (y:B) (xys:list (A*B)) : list (A*B) :=
  (x,y)::remove x xys.

Definition slist : UPO -> UPO.
Admitted.