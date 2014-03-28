Require Import FP.Core.

Inductive v_step S A :=
  | v_Done : v_step S A
  | v_Yield : A -> S -> v_step S A.

Inductive v_stream A := v_Stream
  { v_streamS : Type
  ; v_streamSeed : v_streamS
  ; v_streamStep : v_step v_streamS A
  }.

Definition stream (A:qtype) := lib (v_stream (dom A)).