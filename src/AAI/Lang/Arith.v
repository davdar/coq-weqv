Inductive lang :=
  | Num : nat -> lang
  | Times : lang -> lang -> lang.

Inductive abstract :=
  | Top
  | Even
  | Odd
  | Box.

Fixpoint is_even (n:nat) : bool :=
  match n with
  | O => true
  | S n' => negb (is_even n')
  end.
Fixpoint is_evenp (n:nat) : Prop :=
  match n with
  | O => True
  | S n' => not (is_evenp n')
  end.

Parameter joins : list abstract -> abstract.
Parameter lte : abstract -> abstract -> Prop.
Parameter map : forall {A B}, (A -> B) -> list A -> list B.
Parameter lin : forall {A}, A -> list A -> Prop.
  
(* Standard Galois; can't build gamma *)
Definition alpha (c:list nat) : abstract :=
  joins (map (fun n => 
    match is_even n with
    | true => Even
    | false => Odd
    end) c).

Definition gamma (a:abstract) : list nat.
Abort.

(* using Prop to represent sets, not what we want *)
Definition alpha' (c:nat -> Prop) : abstract -> Prop :=
  fun a => 
    match a with
    | Top => True
    | Even => forall x, c x -> is_evenp x
    | Odd => forall x, c x -> not (is_evenp x)
    | Bot => False
    end.
Definition gamma' (a:abstract -> Prop) : nat -> Prop :=
  fun n =>
    match is_even n with
    | true => forall x, a x -> lte x Even
    | false => forall x, a x -> lte x Odd
    end.

Definition falpha' (c:(nat -> Prop) -> (nat -> Prop)) : (abstract -> Prop) -> abstract -> Prop :=
  fun f => alpha' (c (gamma' f)).
Definition fgamma' (a:(abstract -> Prop) -> (abstract -> Prop)) : (nat -> Prop) -> nat -> Prop :=
  fun f => gamma' (a (alpha' f)).

(* using a weaker notion of galois *)
Definition galois (c:list nat) (a:abstract) : Prop :=
  match a with
  | Top => True
  | Even => forall x, lin x c -> is_evenp x
  | Odd => forall x, lin x c -> not (is_evenp x)
  | Bot => False
  end.

Definition fgalois (cf:list nat -> list nat) (af:abstract -> abstract) : Prop :=
  forall c a, galois c a -> galois (cf c) (af a).
  
  
  