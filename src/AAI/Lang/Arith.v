Require Import FP.Core.
Require Import FP.Data.Nat.
Require Import FP.Data.String.
Require Import FP.Data.ListSet.
Require Import FP.Data.Bool.
Require Import FP.Data.WF.
Require Import FP.Data.Unit.
Require Import FP.Data.Prop.
Require Import FP.Data.PSet.
Require Import FP.Classes.Lattice.
Require Import FP.Classes.Monad.
Require Import FP.Classes.MGalois.

Inductive v_lang :=
  | v_Halt : v_lang
  | v_Times : dom nat -> v_lang -> v_lang.
Definition lang := lib v_lang.
Definition Halt : dom lang := v_Halt.
Definition Times : dom (nat ⇒ lang ⇒ lang) := λ n l → (v_Times : dom nat -> dom lang -> dom lang) n l.
Fixpoint _lang_elim {A} (l:dom lang) : dom (A ⇒ (nat ⇒ A ⇒ A) ⇒ A) := λ h t →
  match l with
  | v_Halt => h
  | v_Times n l => t ∙ n ∙ (_lang_elim l ∙ h ∙ t)
  end.
Definition lang_elim {A} : dom (lang ⇒ A ⇒ (nat ⇒ A ⇒ A) ⇒ A) := λ l → _lang_elim l.
Global Opaque Halt.
Global Opaque Times.
Global Opaque lang_elim.
Ltac lang_induction e :=
  induction e ;
  repeat
    match goal with
    | H : context [v_Halt] |- _ => change v_Halt with Halt in H
    | H : context [v_Times ?n ?l] |- _ => change (v_Times n l) with (Times ∙ n ∙ l) in H
    | |- context [v_Halt] => change v_Halt with Halt
    | |- context [v_Times ?n ?l] => change (v_Times n l) with (Times ∙ n ∙ l)
    end.
Definition lang_elim_beta_Halt {A} (h:dom A) (t:dom (nat ⇒ A ⇒ A)) 
: lang_elim ∙ Halt ∙ h ∙ t ≃ h := libReflexivity.
Definition lang_elim_beta_Times {A} (h:dom A) (t:dom (nat ⇒ A ⇒ A)) n l 
: lang_elim ∙ (Times ∙ n ∙ l) ∙ h ∙ t ≃ t ∙ n ∙ (lang_elim ∙ l ∙ h ∙ t) := libReflexivity.
Definition lang_elim_eta (e:dom lang) : lang_elim ∙ e ∙ Halt ∙ Times ≃ e.
Proof.
  lang_induction e.
  - LibReflexivity.
  - change (Times ∙ d ∙ (lang_elim ∙ e ∙ Halt ∙ Times) ≃ Times ∙ d ∙ e).
    qproper_elim.
Qed.
Ltac LangRewrite :=
  match goal with
  | |- ⟨ lang_elim ∙ Halt ∙ ?h ∙ ?t IN _ |_| _ ⟩ => ReplaceBy (lang_elim_beta_Halt h t)
  | |- ⟨ lang_elim ∙ (Times ∙ ?n ∙ ?l) ∙ ?h ∙ ?t IN _ |_| _ ⟩ => ReplaceBy (lang_elim_beta_Times h t n l)
  | |- ⟨ lang_elim ∙ ?e ∙ Halt ∙ Times IN _ |_| _ ⟩ => ReplaceBy (lang_elim_eta e)
  end.

Inductive v_abstract :=
  | v_Top
  | v_Even
  | v_Odd
  | v_Bot.
Inductive v_abstract_lte : relation v_abstract :=
  | BotLte : forall a, v_abstract_lte v_Bot a
  | TopLte : forall a, v_abstract_lte a v_Top.
Instance : Eqv v_abstract := lib_Eqv.
Instance : Lte v_abstract := { lte := v_abstract_lte }.
Admitted.
Definition abstract := {| qdom := v_abstract |}.
Definition Top : dom abstract := v_Top.
Definition Even : dom abstract := v_Even.
Definition Odd : dom abstract := v_Odd.
Definition Bot : dom abstract := v_Bot.
Definition abstract_elim {A} 
: dom (abstract ⇒ (unit ⇒ A) ⇒ (unit ⇒ A) ⇒ (unit ⇒ A) ⇒ (unit ⇒ A) ⇒ A) := λ a t e o b →
    match a : dom abstract with
    | v_Top => t ∙ tt
    | v_Even => e ∙ tt
    | v_Odd => o ∙ tt
    | v_Bot => b ∙ tt
    end.
Global Opaque Top.
Global Opaque Even.
Global Opaque Odd.
Global Opaque Bot.
Global Opaque abstract_elim.
Ltac abstract_induction e :=
  induction e ;
  repeat
    match goal with
    | H : context [v_Top] |- _ => change v_Top with Top in H
    | H : context [v_Even] |- _ => change v_Even with Even in H
    | H : context [v_Odd] |- _ => change v_Odd with Odd in H
    | H : context [v_Bot] |- _ => change v_Bot with Bot in H
    | |- context [v_Top] => change v_Top with Top
    | |- context [v_Even] => change v_Even with Even
    | |- context [v_Odd] => change v_Odd with Odd
    | |- context [v_Bot] => change v_Bot with Bot
    end.
Definition abstract_elim_beta_Top {A} t e o b
: abstract_elim (A:=A) ∙ Top ∙ t ∙ e ∙ o ∙ b ≃ t ∙ tt := libReflexivity.
Definition abstract_elim_beta_Even {A} t e o b
: abstract_elim (A:=A) ∙ Even ∙ t ∙ e ∙ o ∙ b ≃ e ∙ tt := libReflexivity.
Definition abstract_elim_beta_Odd {A} t e o b
: abstract_elim (A:=A) ∙ Odd ∙ t ∙ e ∙ o ∙ b ≃ o ∙ tt := libReflexivity.
Definition abstract_elim_beta_Bot {A} t e o b
: abstract_elim (A:=A) ∙ Bot ∙ t ∙ e ∙ o ∙ b ≃ b ∙ tt := libReflexivity.
Ltac AbstractRewrite :=
  match goal with
  | |- ⟨ abstract_elim ∙ Top ∙ ?t ∙ ?e ∙ ?o ∙ ?b IN _ |_| _ ⟩ => ReplaceBy (abstract_elim_beta_Top t e o b)
  | |- ⟨ abstract_elim ∙ Even ∙ ?t ∙ ?e ∙ ?o ∙ ?b IN _ |_| _ ⟩ => ReplaceBy (abstract_elim_beta_Even t e o b)
  | |- ⟨ abstract_elim ∙ Odd ∙ ?t ∙ ?e ∙ ?o ∙ ?b IN _ |_| _ ⟩ => ReplaceBy (abstract_elim_beta_Odd t e o b)
  | |- ⟨ abstract_elim ∙ Bot ∙ ?t ∙ ?e ∙ ?o ∙ ?b IN _ |_| _ ⟩ => ReplaceBy (abstract_elim_beta_Bot t e o b)
  end.
                                                  
Inductive v_alang :=
  | v_AHalt : v_alang
  | v_ATimes : dom abstract -> v_alang -> v_alang.
Inductive v_alang_lte : relation v_alang :=
  | AHaltLte : v_alang_lte v_AHalt v_AHalt
  | ATimesLte : forall a₁ a₂ l, a₁ ⊑ a₂ -> v_alang_lte (v_ATimes a₁ l) (v_ATimes a₂ l).
Instance : Eqv v_alang := lib_Eqv.
Instance : Lte v_alang := { lte := v_alang_lte }.
Admitted.
Definition alang := {| qdom := v_alang |}.
Definition AHalt : dom alang := v_AHalt.
Definition ATimes : dom (abstract ⇒ alang ⇒ alang) := λ a al → 
  (v_ATimes : dom abstract -> dom alang -> dom alang) a al.
Fixpoint _alang_elim {A} (al:dom alang)  : dom (A ⇒ (abstract ⇒ A ⇒ A) ⇒ A) := λ hp fp →
  match al with
  | v_AHalt => hp
  | v_ATimes a al => fp ∙ a $ _alang_elim al ∙ hp ∙ fp
  end.
Definition alang_elim {A} : dom (alang ⇒ A ⇒ (abstract ⇒ A ⇒ A) ⇒ A) := λ a → _alang_elim a.
Global Opaque AHalt.
Global Opaque ATimes.
Global Opaque alang_elim.
Ltac alang_induction e :=
  induction e ; 
  repeat
    match goal with
    | H : context [v_AHalt] |- _ => change v_AHalt with AHalt in H
    | H : context [v_ATimes ?a ?al] |- _ => change (v_ATimes a al) with (ATimes ∙ a ∙ al) in H
    | |- context [v_AHalt] => change v_AHalt with AHalt
    | |- context [v_ATimes ?a ?al] => change (v_ATimes a al) with (ATimes ∙ a ∙ al)
    end.
Definition alang_elimM {m A} `{! Monad m } : dom (alang ⇒ A ⇒ (abstract ⇒ A ⇒ m A) ⇒ m A) := λ a hp tp →
  alang_elim ∙ a ∙ (ret ∙ hp) ∙ (λ a r → tp ∙ a =<< r).
Definition alang_elim_beta_AHalt {A} (h:dom A) (f:dom (abstract ⇒ A ⇒ A))
: alang_elim ∙ AHalt ∙ h ∙ f ≃ h := libReflexivity.
Definition alang_elim_beta_ATimes {A} (h:dom A) (f:dom (abstract ⇒ A ⇒ A)) a al
: alang_elim ∙ (ATimes ∙ a ∙ al) ∙ h ∙ f ≃ f ∙ a ∙ (alang_elim ∙ al ∙ h ∙ f) := libReflexivity.
Definition alang_elim_eta (e:dom alang) : alang_elim ∙ e ∙ AHalt ∙ ATimes ≃ e.
Proof.
  alang_induction e.
  - LibReflexivity.
  - change (ATimes ∙ d ∙ (alang_elim ∙ e ∙ AHalt ∙ ATimes) ≃ ATimes ∙ d ∙ e).
    qproper_elim.
Qed.
Ltac AlangRewrite :=
  match goal with
  | |- ⟨ alang_elim ∙ AHalt ∙ ?h ∙ ?f IN _ |_| _ ⟩ => ReplaceBy (alang_elim_beta_AHalt h f)
  | |- ⟨ alang_elim ∙ (ATimes ∙ ?a ∙ ?al) ∙ ?h ∙ ?f IN _ |_| _ ⟩ => ReplaceBy (alang_elim_beta_ATimes h f a al)
  | |- ⟨ alang_elim ∙ ?e ∙ AHalt ∙ ATimes IN _ |_| _ ⟩ => ReplaceBy (alang_elim_eta e)
  end.

Instance : Lattice alang.
Admitted.

Definition decEven : dom (nat ⇒ bool) := undefined.

Inductive v_isEven : dom nat -> Prop :=
  | ZEven : v_isEven vZ
  | SEven : forall n, v_isEven n -> v_isEven (vS (vS n)).
Inductive v_isOdd : dom nat -> Prop :=
  | ZOdd : v_isOdd (vS vZ)
  | SOdd : forall n, v_isOdd n -> v_isOdd (vS (vS n)).

Definition isEven : dom (nat ⇒ prop) := λ n → v_isEven n : dom prop.
Definition isOdd : dom (nat ⇒ prop) := λ n → v_isOdd n : dom prop.

Definition αnat : dom (nat ⇒ abstract) := λ n →
  case ∙ (decEven ∙ n) ∙ (λ _ → Even) ∙ (λ _ → Odd).
Definition γTop : dom (wfT listSet nat) := wfT_fix $ λ γTop →
  ret ∙ Z m+ ret ∙ (S ∙ γTop).
Definition γTop2 : dom (pset nat) := suniversal.

Definition γEven : dom (wfT listSet nat) := wfT_fix $ λ γEven →
  ret ∙ Z m+ ret ∙ (S $ S ∙ γEven).
Definition γEven2 : dom (pset nat) := PSet ∙ isEven.

Definition γOdd : dom (wfT listSet nat) := wfT_fix $ λ γOdd →
  ret ∙ (S ∙ Z) m+ ret ∙ (S $ S ∙ γOdd).
Definition γOdd2 : dom (pset nat) := PSet ∙ isOdd.

Definition γnat : dom (abstract ⇒ wfT listSet nat) := λ a →
  abstract_elim ∙ a
    ∙ (λ _ → γTop)
    ∙ (λ _ → γEven)
    ∙ (λ _ → γOdd)
    ∙ (λ _ → mzero).

Instance : MGalois (wfT listSet) nat abstract :=
  { mgaloisα := kret ∙ αnat
  ; mgaloisγ := γnat
  }.
Proof.
  - qproper_elim.
    Re fail || match goal with |- ⟨ y IN _ |_| _ ⟩ => StrengthenBy H end.
    clear H y.
    abstract_induction x ; Re fail || AbstractRewrite.
    + admit.
    + unfold γEven.
      EnterLeft ; PushFun ; PushArg.
      match goal with |- ⟨ wfT_fix ∙ ?f IN _ |_| _ ⟩ => ReplaceBy (wfT_fix_beta f) end.
      PopArg ; PopFun ; ExitLeft.
      Re fail || MonadRewrite.
      simpl.
    + admit.
    + admit.
  - admit.
Defined.

(* (nat -> Prop) -> nat -> anat


     abs : nat -> anat
     conc : anat -> nat -> Prop

     forall n, conc (abs n) n     (soundness)
     forall a, (forall n, (conc a) n -> abs n = a)

     step_conc : nat -> nat
     step_abs  : anat -> anat

     1. forall n, abs (step_conc n) <= step_abs (abs n)
     2. forall a, (forall n, conc a n -> 
                      abs (conc_step n) <= abs_step a)
*)



Definition αlang : dom (lang ⇒ alang) := λ l →
  lang_elim ∙ l ∙ AHalt $ λ n al → ATimes ∙ (αnat ∙ n) ∙ al.
Definition αlangM : dom (lang ⇒ wfT listSet alang) := kret ∙ αlang.
Definition γlangM : dom (alang ⇒ wfT listSet lang) := λ a →
  alang_elimM ∙ a ∙ Halt $ λ a l → 
    n ← γnat ∙ a ;;
    ret $ Times ∙ n ∙ l.

Section MGalois.
  Instance : MGalois (wfT listSet) lang alang :=
    { mgaloisα := αlangM
    ; mgaloisγ := γlangM
    }.
  Proof.
    - Local Opaque αnat.
      Local Opaque γnat.
      Local Opaque γlangM.
      apply qmonotonic_intro ; unfold "⇉" ; intros ; simpl.
      Re fail || match goal with |- ⟨ y IN _ |_| _ ⟩ => StrengthenBy H end.
      clear H y.
      alang_induction x ; Re fail || LangRewrite || AlangRewrite || MonadRewrite.
      EnterLeft.
 Admitted.
End MGalois.
      (*
      ReplaceBy (bind_associativity (A:=abstract) (alang_elim ∙  _ αlangM).
      MonadRewrite.
      PushFun.
      PushArg.
      apply (lte_replace_lte IHx).
      WeakenBy IHx.
      Re fail || WeakenBy IHx.
      idtac.
      match goal with
      | IHx : ?t |- _ => assert t
      end.
      Re fail || LangRewrite || AlangRewrite || MonadRewrite.
      epose (_=IHx).
      eapply IHx.
      + simpl.
      match goal with
      | |- context E[ alang_elimM ∙ ?e ∙ _ ∙ _ ] => eapply alang_indM (typeof E) _ _ 
      Re fail || MonadRewrite.
      Re fail || match goal with |- ⟨ x IN _ |LTE| _ ⟩ => WeakenBy H end.
      EnterLeft.
      PushFun.
      PushArg.
      PushFun.
      PushFun.
      PushArg.
      apply (replaceBy H).
      simpl.
*)
