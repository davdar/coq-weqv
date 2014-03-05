Require Import FP.Core.QType.
Require Import FP.Core.Universe.
Require Import FP.Core.Relations.

Local Instance inj_Eqv {A B} `{! Eqv B } (inj:A -> B) : Eqv A :=
  { eqv x y := eqv (inj x) (inj y) }.
Proof.
  constructor ; simpl ; intros.
  - LibReflexivity.
  - Symmetry ; auto.
  - Transitivity (inj y) ; auto.
Defined.

Local Instance inj_Lte {A B} `{! Eqv B ,! Lte B } (inj:A -> B) 
: Lte (Eqv0:=inj_Eqv inj) A :=
  { lte x y := lte (inj x) (inj y) }.
Proof.
  constructor ; simpl ; intros.
  - Reflexivity ; auto.
  - Transitivity (inj y) ; auto.
Defined.

Definition derive A {τ} (inj:A -> dom τ) : qtype :=
  {| qdom := A 
   ; qEqv := inj_Eqv inj
   ; qLte := inj_Lte inj
  |}.