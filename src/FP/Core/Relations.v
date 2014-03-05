Definition relation (A:Type) := A -> A -> Prop.
Definition rel_neg {A} (R:relation A) : relation A := fun x y => not (R x y).
Definition proper {A:Type} (R:relation A) (x:A) := R x x.
Arguments proper {A} R x /.

Class LibReflexive {A} (R:relation A) := libReflexivity : forall (x:A), R x x.
Arguments LibReflexive {A} R /.
Ltac LibReflexivity := apply libReflexivity.

Class Symmetric {A} (R:relation A) := symmetry : forall (x y:A), R x y -> R y x.
Arguments Symmetric {A} R /.
Ltac Symmetry := apply symmetry.

Class Transitive {A} (R:relation A) := transitivity : forall (x y z:A), R x y -> R y z -> R x z.
Arguments Transitive {A} R /.
Ltac Transitivity y := apply (transitivity _ y _).

Class Equivalence {A} (R:relation A) :=
  { Equivalence_LibReflexive :> LibReflexive R
  ; Equivalence_Symmetric :> Symmetric R
  ; Equivalence_Transitive :> Transitive R
  }.

Class Eqv (A:Type) :=
  { eqv : relation A 
  ; Eqv_Equivalence :> Equivalence eqv
  }.
Arguments eqv {A Eqv} f g : simpl never.
Infix "≃" := eqv (at level 50, no associativity).
Infix "≄" := (rel_neg eqv) (at level 50, no associativity).

Class Reflexive {A:Type} `{! Eqv A } (R:relation A) := 
  reflexivity : forall x y, eqv x y -> R x y.
Arguments Reflexive {A _} R /.
Ltac Reflexivity := apply reflexivity.

Class PreOrder {A:Type} `{! Eqv A } (R:relation A) :=
  { PreOrder_Reflexive :> Reflexive R
  ; PreOrder_Transitive :> Transitive R
  }.

Class Lte (A:Type) `{! Eqv A } :=
  { lte : relation A
  ; Lte_PreOrder :> PreOrder lte
  }.
Arguments lte {A Eqv0 Lte} f g : simpl never.
Infix "⊑" := lte (at level 50, no associativity).

Instance : forall A `{! Eqv A } (R:relation A) `{! PreOrder R }, LibReflexive R.
Proof.
  simpl ; intros.
  Reflexivity ; LibReflexivity.
Defined.

Section lib_eqv.
  Local Instance lib_Eqv {A} : Eqv A := { eqv := eq }.
  Admitted.
End lib_eqv.

Section trivial_lte.
  Local Instance trivial_Lte {A} `{! Eqv A } : Lte A := { lte := eqv }.
  Proof.
    constructor ; simpl ; intros ; auto.
    Transitivity y ; auto.
  Defined.
End trivial_lte.

Section dual_lte.
  Local Instance dualLte {A} `{! Eqv A ,! Lte A } : Lte A := { lte x y := lte y x }.
  Proof.
    constructor ; simpl ; intros.
    - Reflexivity ; Symmetry ; auto.
    - Transitivity y ; auto.
  Defined.
End dual_lte.

Class DecEqv A `{! Eqv A } := { dec_eqv : forall (x y:A), x ≃ y \/ x ≄ y }.

Definition vrespectful {A B} (R1:relation A) (R2:relation B) : relation (A -> B) :=
  fun (f g:A -> B) => forall x y, R1 x y -> R2 (f x) (g y).
Arguments vrespectful {A B} R1 R2 f g : simpl never.
Infix "v⇉" := vrespectful (at level 60, right associativity).