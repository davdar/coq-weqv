Require Import FP.Core.
Require Import FP.Data.Nat.
Require Import FP.Classes.Monad.
Require Import FP.Classes.Injection.
Require Import FP.Classes.Lattice.
Require Import FP.Classes.Injection.

Definition wf_nat_lte {m:qtype -> qtype} {A} 
: relation (dom nat -> dom (m A)) := fun f g => forall m, exists n, f m ⊑ g n.
Definition wf_nat_eqv {m:qtype -> qtype} {A} 
: relation (dom nat -> dom (m A)) := fun x y => wf_nat_lte x y /\ wf_nat_lte y x.

Inductive v_wfT (m:qtype -> qtype) A := v_WfT
  { v_unWfT : dom (nat ⇒ m A) }.
Arguments v_WfT {m A} _.
Arguments v_unWfT {m A} _.

Definition wfT m A := derive (v_wfT m A) v_unWfT.

Definition WfT {m A} : dom ((nat ⇒ m A) ⇒ wfT m A) := λ f → v_WfT f : dom (wfT m A).
Definition unWfT {m A} : dom (wfT m A ⇒ nat ⇒ m A) := λ aM → v_unWfT (aM : dom (wfT m A)).
Global Opaque WfT.
Global Opaque unWfT.

Instance : forall m A, InjectionEqv (@unWfT m A) :=
  { injectionEqv _x _y p := p }.
Instance : forall m A, InjectionLte (@unWfT m A) :=
  { injectionLte _x _y p := p }.
Definition WfT_inv {m A} (f:dom (nat ⇒ m A)) 
: unWfT ∙ (WfT ∙ f) ≃ f := libReflexivity.
Ltac WfTRewrite :=
  match goal with
  | |- ⟨ unWfT ∙ (WfT ∙ ?f) ∙ ?x IN ?k |?m| ?y ⟩ => change ⟨ f ∙ x IN k |m| y ⟩
  | |- ⟨ unWfT ∙ (WfT ∙ ?f) IN _ |_| _ ⟩ => ReplaceBy (WfT_inv f)
  end.

Definition wfT_ret {m} `{! Monad m } {A} : dom (A ⇒ wfT m A) := λ x → WfT $ λ _ → ret ∙ x.
Definition wfT_bind {m} `{! Monad m } {A B} : dom (wfT m A ⇒ (A ⇒ wfT m B) ⇒ wfT m B) := λ aM k →
  WfT $ λ n →
    a ← unWfT ∙ aM ∙ n ;;
    unWfT ∙ (k ∙ a) ∙ n.
Instance : forall m `{! Monad m }, Monad (wfT m) :=
  { ret := @wfT_ret _ _
  ; bind := @wfT_bind _ _
  }. admit. admit. admit. Defined.
Definition wfT_mret {m} `{! Monad m } {A} : dom (m A ⇒ wfT m A) := λ aM → WfT $ λ _ → aM.
Instance : MonadRet wfT :=
  { mret := @wfT_mret }.
Instance : forall m `{! Monad m ,! MonadPlus m }, MonadPlus (wfT m).
Admitted.

Definition wfT_fix {m A} `{! Monad m ,! MonadPlus m } : dom ((A ⇒ wfT m A) ⇒ wfT m A) := 
  λ f → WfT $ λ n →
  (fix loop n :=
    match n with
    | O => mzero
    | Coq.Init.Datatypes.S n' => 
        x ← loop n' ;;
        unWfT ∙ (f ∙ x) ∙ n 
    end) (n:dom nat).
Definition wfT_fix_beta_Z {m A} `{! Monad m ,! MonadPlus m } (f:dom (A ⇒ wfT m A)) 
: unWfT ∙ (wfT_fix ∙ f) ∙ Z ≃ mzero := libReflexivity.
Definition wfT_fix_beta_S {m A} `{! Monad m ,! MonadPlus m } (f:dom (A ⇒ wfT m A)) (n:dom nat)
: unWfT ∙ (wfT_fix ∙ f) ∙ (S ∙ n) ≃ (x ← unWfT ∙ (wfT_fix ∙ f) ∙ n ;; unWfT ∙ (f ∙ x) ∙ (S ∙ n)) := libReflexivity.

(*
Definition wfT_eqv_intro {m A} (f g:dom nat -> dom (m A)) (p:wf_nat_eqv f g) : WFT_unsafe f ≃ WFT_unsafe g := p.
Definition wfT_eqv_elim {m A} (f g:dom nat -> dom (m A)) (p:WFT_unsafe f ≃ WFT_unsafe g) : wf_nat_eqv f g := p.

Definition wfT_lte_intro {m A} (f g:dom nat -> dom (m A)) (p:wf_nat_lte f g) : WFT_unsafe f ⊑ WFT_unsafe g := p.
Definition wfT_lte_elim {m A} (f g:dom nat -> dom (m A)) (p:WFT_unsafe f ⊑ WFT_unsafe g) : wf_nat_lte f g := p.
*)

Definition later {m A} : dom (wfT m A ⇒ wfT m A) := λ aM → WfT $ λ n →
  unWfT ∙ aM ∙ (pred ∙ n).

Section Beta.

  Definition wfT_fix_beta {m A} `{! Monad m ,! MonadPlus m } (f:dom (A ⇒ wfT m A)) 
  : wfT_fix ∙ f ≃ (f =<< later ∙ (wfT_fix ∙ f)).
  Proof.
    unfold later,extend.
    Local Transparent bind.
    unfold bind.
    Local Opaque bind.
    simpl.
    apply (injectionEqv unWfT).
    apply qproper_intro ; unfold respectful ; intros ; simpl.
    Re fail || WfTRewrite.
    Re fail || match goal with |- ⟨ x IN _ |_| _ ⟩ => ReplaceBy H end.
    clear x H.
    nat_induction y ; Re fail || NatRewrite || MonadRewrite.
    - Local Transparent wfT_fix.
      unfold wfT_fix.
      Local Opaque wfT_fix.
      Re fail || WfTRewrite.
      Local Transparent Z.
      unfold Z.
      Local Opaque Z.
      Re fail || MonadPlusRewrite.
    - Re fail || MonadRewrite.
    Local Transparent bind.
    unfold bind at 2.
    Local Opaque bind.
    Re fail || WfTRewrite.
    nat_induction x.
    - Re fail || WfTRewrite || NatRewrite.
      Local Transparent Z.
      unfold Z.
      Local Opaque Z.
      Re fail || MonadPlusRewrite.
    - Local Transparent bind.
      unfold bind at 3.
      Local Opaque bind.
      Re fail || WfTRewrite || NatRewrite.
      eapply IHx.
      cbv
      simpl.
      Symmetry.
      EnterLeft.
      match goal with |- ⟨ unWfT ∙ (WfT ∙ ?f) ∙ ?x IN ?k |EQV| ?y ⟩ => change ⟨ f ∙ x IN k |EQV| y ⟩ end.
      PushArg.

      Re fail || WfTRewrite.

      EnterRight. 
      WfTRewrite.
      Re fail || WfTRewrite.
    qproper_elim.
    appl
    match goal with
    |- ?x ≃ ?y => Transitivity (WFT_unsafe (v_unWFT y))
    end.
    - Local Transparent bind.
      Local Transparent mret.
      simpl.
      Local Opaque bind.
      Local Opaque mret.
      apply wfT_eqv_intro ; unfold wf_nat_eqv,wf_nat_lte ; split ; intros.
      + exists m0.
        induction m0.
        * admit.
        * EnterLeft ; PushFun ; PushArg.
            WeakenBy IHm0.
          PopArg ; PopFun ; ExitLeft.
          Re fail || MonadRewrite.
          admit.
      + exists (Coq.Init.Datatypes.S m0).
        Re fail || MonadRewrite.
        admit.
    - admit.
  Qed.
End Beta.

Definition wfProp := dom nat -> Prop.

Definition wf_lte {m} `{! Monad m } {A} (x:dom (wfT m A)) (y:dom (wfT m A)) : wfProp := fun m => exists n, v_unWFT x m ⊑ v_unWFT y n.

Definition wf_eqv {m} `{! Monad m } {A} (x:dom (wfT m A)) (y:dom (wfT m A)) : wfProp := fun n => wf_lte x y n /\ wf_lte y x n.

Definition wfDen : wfProp -> Prop := fun p => forall n, p n.

Goal forall m A `{! Monad m } (xM yM:dom (wfT m A)), (wfDen (wf_eqv xM yM)) -> xM ≃ yM.
Admitted.