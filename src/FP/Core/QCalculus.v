Require Import FP.Core.QType.
Require Import FP.Core.RFunction.
Require Import FP.Core.Universe.
Require Import FP.Core.Relations.
Require Import Coq.Program.Equality.

Local Reserved Notation "τ ∈ Γ" (at level 88, no associativity).
Local Reserved Notation "Γ ⊢ τ" (at level 88, no associativity).
Local Reserved Notation "Γ₁ ⊆ Γ₂" (at level 90, no associativity).
Local Reserved Notation "Γ₁ ≼ Γ₂" (at level 90, no associativity).

Local Infix "∷" := cons (at level 60, right associativity).

(********** The Language **********)

Inductive var : qtype -> list qtype -> Type :=
  | HeadVar : forall {Γ τ}, τ ∈ τ∷Γ
  | TailVar : forall {Γ τ₁ τ₂}, τ₂ ∈ Γ -> τ₂ ∈ τ₁∷Γ
where "τ ∈ Γ" := (var τ Γ).

Inductive oterm : list qtype -> qtype -> Type :=
  | Val : 
      forall {Γ τ},
      dom τ -> 
      Γ ⊢ τ
  | Var :
      forall {Γ τ},
      τ ∈ Γ -> 
      Γ ⊢ τ
  | Abs : 
      forall {Γ τ₁ τ₂},
      τ₁∷Γ ⊢ τ₂ ->
      Γ ⊢ (τ₁ ⇒ τ₂)
  | App :
      forall {Γ τ₁ τ₂},
      Γ ⊢ τ₁ ⇒ τ₂ ->
      Γ ⊢ τ₁ ->
      Γ ⊢ τ₂
where "Γ ⊢ τ" := (oterm Γ τ).
Definition term τ := nil ⊢ τ.
Inductive env : list qtype -> Type :=
  | NullEnv : env nil
  | ConsEnv : forall {Γ τ}, dom τ -> env Γ -> env (τ∷Γ).
Inductive renaming : list qtype -> list qtype -> Type :=
  | NullRenaming : forall {Γ}, nil ⊆ Γ
  | ConsRenaming : forall {Γ₁ Γ₂ τ}, τ ∈ Γ₂ -> Γ₁ ⊆ Γ₂ -> τ∷Γ₁ ⊆ Γ₂
where "Γ₁ ⊆ Γ₂" := (renaming Γ₁ Γ₂).
Inductive substitution : list qtype -> list qtype -> Type :=
  | NullSubstitution : forall {Γ}, nil ≼ Γ
  | ConsSubstitution : forall {Γ₁ Γ₂ τ}, Γ₂ ⊢ τ -> Γ₁ ≼ Γ₂ -> τ∷Γ₁ ≼ Γ₂
where "Γ₁ ≼ Γ₂" := (substitution Γ₁ Γ₂).

(********** renaming **********)

(***** renaming primitives *****)

Fixpoint weaken_renaming {Γ₁ Γ₂ τ} (δ:Γ₁ ⊆ Γ₂) : Γ₁ ⊆ τ∷Γ₂ :=
  match δ with
  | NullRenaming _ => NullRenaming
  | ConsRenaming _ _ _ x δ' => ConsRenaming (TailVar x) (weaken_renaming δ')
  end.
Fixpoint identity_renaming {Γ} : Γ ⊆ Γ :=
  match Γ with
  | nil => NullRenaming
  | τ∷_ => ConsRenaming HeadVar (weaken_renaming identity_renaming)
  end.
Definition push_renaming {Γ τ} : Γ ⊆ τ∷Γ := weaken_renaming identity_renaming.
Definition cons_renaming {Γ₁ Γ₂ τ} (δ:Γ₁ ⊆ Γ₂) : τ∷Γ₁ ⊆ τ∷Γ₂ := 
  ConsRenaming HeadVar (weaken_renaming δ).
Definition exchange_renaming {Γ τ₁ τ₂} : τ₁∷τ₂∷Γ ⊆ τ₂∷τ₁∷Γ :=
  ConsRenaming (TailVar HeadVar) (ConsRenaming HeadVar (weaken_renaming push_renaming)).

(***** renaming applications *****)

Fixpoint rename_var {Γ₁ Γ₂ τ} (δ:Γ₁ ⊆ Γ₂) (x:τ ∈ Γ₁) : τ ∈ Γ₂ :=
  match x in τ ∈ Γ₁ 
  return Γ₁ ⊆ Γ₂ -> τ ∈ Γ₂
  with
  | HeadVar Γ₁' τ => fun (δ:τ∷Γ₁' ⊆ Γ₂) =>
      match δ with ConsRenaming _ _ _ x' _ => x' end
  | TailVar Γ₁' τ' τ x' => fun (δ:τ'∷Γ₁' ⊆ Γ₂) =>
      match δ in Γ₁ ⊆ Γ₂ 
      return
        match Γ₁ with
        | nil => unit
        | τ'∷Γ₁' => τ ∈ Γ₁' -> τ ∈ Γ₂
        end
      with 
      | NullRenaming _ => tt
      | ConsRenaming Γ₁' _ _ _ δ' => fun (x':τ ∈ Γ₁') => 
          rename_var δ' x'
      end x'
  end δ.
Fixpoint trans_renaming {Γ₁ Γ₂ Γ₃} (δ₂:Γ₂ ⊆ Γ₃) (δ₁:Γ₁ ⊆ Γ₂) : Γ₁ ⊆ Γ₃ :=
  match δ₁ in Γ₁ ⊆ Γ₂ return Γ₂ ⊆ Γ₃ -> Γ₁ ⊆ Γ₃ with
  | NullRenaming Γ₂ => fun _ => NullRenaming
  | ConsRenaming _ _ _ x δ₁' => fun δ₂ => ConsRenaming (rename_var δ₂ x) (trans_renaming δ₂ δ₁')
  end δ₂.

Fixpoint rename_term {Γ₁ Γ₂ τ} (δ:Γ₁ ⊆ Γ₂) (e:Γ₁ ⊢ τ) : Γ₂ ⊢ τ :=
  match e in Γ₁ ⊢ τ return Γ₁ ⊆ Γ₂ -> Γ₂ ⊢ τ with
  | Val _ _ v => fun _ => Val v
  | Var Γ₁ _ x => fun (δ:Γ₁ ⊆ Γ₂) => Var (rename_var δ x)
  | Abs Γ₁ _ _ e => fun (δ:Γ₁ ⊆ Γ₂) => Abs (rename_term (cons_renaming δ) e)
  | App Γ₁ _ _ e₁ e₂ => fun (δ:Γ₁ ⊆ Γ₂) => App (rename_term δ e₁) (rename_term δ e₂)
  end δ.
Definition push_term {Γ τ₁ τ₂} : Γ ⊢ τ₁ -> τ₂∷Γ ⊢ τ₁ := rename_term push_renaming.

(********** reduction **********)

Definition cut_var {Γ₁ Γ₂ τ₁ τ₂} (θ:Γ₂ ⊆ τ₁∷Γ₁) (e:Γ₁ ⊢ τ₁) (x:τ₂ ∈ Γ₂) : Γ₁ ⊢ τ₂ :=
  match rename_var θ x in τ₂ ∈ Γ' return
    match Γ' with
    | nil => unit
    | τ₁∷Γ₁ => Γ₁ ⊢ τ₁ -> Γ₁ ⊢ τ₂
    end
  with
  | HeadVar Γ₂ τ₁ => fun e => e
  | TailVar Γ₂ τ₁ τ₂ x' => fun _ => Var x'
  end e.
    

Fixpoint cut_strong {Γ₁ Γ₂ τ₁ τ₂} (θ:Γ₂ ⊆ τ₁∷Γ₁) (e:Γ₁ ⊢ τ₁) (f:Γ₂ ⊢ τ₂) : Γ₁ ⊢ τ₂ :=
  match f in Γ₂ ⊢ τ₂ return Γ₂ ⊆ τ₁∷Γ₁ -> Γ₁ ⊢ τ₁ -> Γ₁ ⊢ τ₂ with
  | Val _ _ v => fun _ _ => Val v
  | Var Γ₂ τ₂ x => fun θ e => cut_var θ e x
  | Abs Γ₂ τ₁' τ₂' e' => fun θ e =>
      let θ' := trans_renaming exchange_renaming (cons_renaming θ) in
      Abs (cut_strong θ' (push_term e) e')
  | App Γ₂ τ₁' τ₂ e₁ e₂ => fun θ e => App (cut_strong θ e e₁) (cut_strong θ e e₂)
  end θ e.

Definition cut {Γ τ₁ τ₂} : Γ ⊢ τ₁ -> τ₁∷Γ ⊢ τ₂ -> Γ ⊢ τ₂ := cut_strong identity_renaming.

(********** [env] relations and respectful properties **********)

Inductive env_eqv : forall Γ, relation (env Γ) :=
  | NullEnvEqv : env_eqv nil NullEnv NullEnv
  | ConsEnvEqv : forall τ Γ v₁ v₂ ρ₁ ρ₂, 
      v₁ ≃ v₂ -> 
      env_eqv Γ ρ₁ ρ₂ -> 
      env_eqv (τ∷Γ) (ConsEnv v₁ ρ₁) (ConsEnv v₂ ρ₂) .
Instance : forall Γ, Eqv (env Γ) := { eqv := env_eqv Γ }.
Proof.
  constructor ; simpl ; intros.
  - induction x ; constructor ; auto ; LibReflexivity.
  - induction H ; constructor ; auto.
    Symmetry ; auto.
  - induction H ; auto.
    dependent destruction z.
    dependent destruction H0.
    constructor ; auto.
    Transitivity v₂ ; auto.
Defined.

Inductive env_lte : forall Γ, relation (env Γ) :=
  | NullEnvLte : env_lte nil NullEnv NullEnv
  | ConsEnvLte : forall τ Γ v₁ v₂ ρ₁ ρ₂,
      v₁ ⊑ v₂ ->
      env_lte Γ ρ₁ ρ₂ ->
      env_lte (τ∷Γ) (ConsEnv v₁ ρ₁) (ConsEnv v₂ ρ₂).
Instance : forall Γ, Lte (env Γ) := { lte := env_lte Γ }.
Proof.
  constructor ; simpl ; intros.
  - induction H ; constructor ; auto.
    Reflexivity ; auto.
  - induction H ; auto.
    dependent destruction z.
    dependent destruction H0.
    constructor ; auto.
    Transitivity v₂ ; auto.
Defined.

Definition QConsEnv {Γ τ} : dom τ r⇒ env Γ r⇒ env (τ∷Γ).
refine( rλ v ρ → ConsEnv v ρ ).
Proof.
  - constructor ; rproper.
  - constructor ; rproper.
Grab Existential Variables.
  + constructor ; rproper.
  + constructor ; rproper.
Defined.
Arguments QConsEnv : simpl never.

(********** [lookup] and respectful properties **********)

Fixpoint lookup {Γ τ} (x:τ ∈ Γ) {struct x} : env Γ r⇒ dom τ.
refine(
  match x in τ ∈ Γ return env Γ r⇒ dom τ with
  | HeadVar Γ' τ => rλ (ρ:env (τ∷Γ')) → 
      match ρ in env Γ return
        match Γ with
        | nil => unit : Type
        | τ∷Γ' => dom τ
        end
      with 
      | NullEnv => tt
      | ConsEnv _ _ e _ => e 
      end
  | TailVar Γ' τ' τ x' => rλ (ρ:env (τ'∷Γ')) → 
      match ρ in env Γ return
        match Γ with
        | nil => unit : Type
        | τ'∷Γ' => τ ∈ Γ' -> dom τ
        end
      with 
      | NullEnv => tt
      | ConsEnv _ _ _ ρ' => fun x' => lookup _ _ x' r∙ ρ'
      end x'
  end
) ; rproper.
Proof.
  - dependent destruction x0.
    dependent destruction y.
    unfold eqv in H ; simpl in H ; dependent destruction H ; auto.
  - dependent destruction x0.
    dependent destruction y.
    unfold lte in H ; simpl in H ; dependent destruction H ; auto.
  - dependent destruction x0.
    dependent destruction y ; rproper.
    unfold eqv in H ; simpl in H ; dependent destruction H ; auto.
  - dependent destruction x0.
    dependent destruction y ; rproper.
    unfold lte in H ; simpl in H ; dependent destruction H ; auto.
Defined.

(********** denotation for [oterm] **********)

Definition denote_val {Γ τ} (v:dom τ) : env Γ r⇒ dom τ := rconst r∙ v.
Arguments denote_val : simpl never.

Definition denote_var {Γ τ} (x:τ ∈ Γ) : env Γ r⇒ dom τ := lookup x.
Arguments denote_var : simpl never.

Definition denote_abs {Γ τ₁ τ₂} (f:env (τ₁∷Γ) r⇒ dom τ₂) : env Γ r⇒ dom (τ₁ ⇒ τ₂).
refine( rλ ρ e → f r∙ (QConsEnv r∙ e r∙ ρ) ) ; rproper.
Proof.
  - apply (rfun_proper QConsEnv) ; rproper.
  - apply (rfun_monotonic QConsEnv) ; rproper.
Grab Existential Variables.
  + rproper ; apply (rfun_monotonic QConsEnv) ; rproper.
  + rproper ; apply (rfun_proper QConsEnv) ; rproper.
Defined.
Arguments denote_abs : simpl never.

Definition denote_app {Γ τ₁ τ₂} (f:env Γ r⇒ dom (τ₁ ⇒ τ₂)) (e:env Γ r⇒ dom τ₁) : env Γ r⇒ dom τ₂.
refine( rλ ρ → f r∙ ρ r∙ (e r∙ ρ) ) ; rproper ; rproper_elim ; rproper.
Defined.
Arguments denote_app : simpl never.

Fixpoint denote_strong {Γ τ} (e:Γ ⊢ τ) : env Γ r⇒ dom τ :=
  match e in Γ ⊢ τ return env Γ r⇒ dom τ with
  | Val _ _ v => denote_val v
  | Var _ _ x => denote_var x
  | Abs _ _ _ e' => denote_abs (denote_strong e')
  | App _ _ _ e₁ e₂ => denote_app (denote_strong e₁) (denote_strong e₂)
  end.
Definition denote {τ} (e:term τ) : dom τ := denote_strong e r∙ NullEnv.

(********** [oterm] relations **********)

Instance : forall Γ τ, Eqv (Γ ⊢ τ) := { eqv e₁ e₂ := denote_strong e₁ ≃ denote_strong e₂ }.
Proof.
  constructor ; simpl ; intros.
  - LibReflexivity.
  - Symmetry ; auto.
  - Transitivity (denote_strong y) ; auto.
Defined.

(********** building terms **********)

Definition abs {Γ τ₁ τ₂} (f:τ₁∷Γ ⊢ τ₁ -> τ₁∷Γ ⊢ τ₂)
: Γ ⊢ (τ₁ ⇒ τ₂) := Abs (f (Var HeadVar)).

Inductive ARN : list qtype -> list qtype -> Type :=
  | NullARN : forall Γ, ARN Γ Γ
  | ConsARN : forall Γ₁ Γ₂ τ, ARN Γ₁ Γ₂ -> ARN Γ₁ (τ∷Γ₂).
Class AutoRename Γ₁ Γ₂ := auto_rename : ARN Γ₁ Γ₂.
Instance : forall Γ₁ Γ₂ τ `{! AutoRename Γ₁ Γ₂ }, AutoRename Γ₁ (τ∷Γ₂) := ConsARN.
Instance : forall Γ, AutoRename Γ Γ := NullARN.
Definition lift_ARN {Γ₁ Γ₂ τ} (arn:ARN Γ₁ Γ₂) (e:Γ₁ ⊢ τ) : Γ₂ ⊢ τ.
Proof.
  induction arn ; auto.
  apply (rename_term (weaken_renaming identity_renaming)) ; auto.
Defined.
Definition lift {Γ₁ Γ₂ τ} `{! AutoRename Γ₁ Γ₂ } : Γ₁ ⊢ τ -> Γ₂ ⊢ τ := lift_ARN auto_rename.
Definition app {Γ₁ Γ₂ Γ₃ τ₁ τ₂} `{! AutoRename Γ₁ Γ₃ ,! AutoRename Γ₂ Γ₃ }
(f:Γ₁ ⊢ τ₁ ⇒ τ₂) (e:Γ₂ ⊢ τ₁) : Γ₃ ⊢ τ₂ := App (lift f) (lift e).
  
Local Notation "'tλ'  x .. y → e" := (abs (fun x => .. (abs (fun y => e)) ..))
  (x binder, y binder, at level 100, right associativity).
Local Infix "∙" := app (at level 20, left associativity).
Local Notation "^ x" := (lift x) (at level 1).

(********** simple functions and laws **********)

(*
Possibly necessary for continuing
Fixpoint rename_env {Γ₁ Γ₂ τ} (θ:Γ₁ ⊆ Γ₂) {struct θ} : (env Γ₁ r⇒ dom τ) r⇒ (env Γ₂ r⇒ dom τ).
refine(
  match θ in Γ₁ ⊆ Γ₂ return (env Γ₁ r⇒ dom τ) r⇒ (env Γ₂ r⇒ dom τ) with
  | NullRenaming Γ₂ => rλ e → rconst r∙ (e r∙ NullEnv)
  | ConsRenaming Γ₁' Γ₂ τ' x' θ' => rλ e ρ₂ → 
      rename_env _ _ _ θ' r∙ (rλ ρ₁' → e r∙ 
        (QConsEnv r∙ (lookup x' r∙ ρ₂) r∙ ρ₁')) r∙ ρ₂

  end
).
Proof.
  - rproper.
  - rproper.
  - rproper.
    apply rename_env ; rproper.
    apply QConsEnv ; rproper.
  - rproper.
    apply rename_env ; rproper.
    apply QConsEnv ; rproper.
Grab Existential Variables.
  * rproper.
    apply rename_env ; rproper.
    apply QConsEnv ; rproper.
  * rproper.
    apply rename_env ; rproper.
    apply QConsEnv ; rproper.
  * rproper.
    apply QConsEnv ; rproper.
  * rproper.
    apply QConsEnv ; rproper.
Defined.
*)

Definition cut_eqv Γ₁ Γ₂ τ₁ τ₂ (θ:Γ₂ ⊆ τ₁∷Γ₁) (e:Γ₁ ⊢ τ₁) (f:Γ₂ ⊢ τ₂) 
: denote_strong (Abs (rename_term θ f) ∙ e) ≃ denote_strong (cut_strong θ e f).
Proof.
Abort.
(*
  generalize dependent e.
  generalize dependent θ.
  generalize dependent Γ₁.
  dependent induction f ; intros ; simpl.
  - unfold denote_app,denote_abs,denote_val ; simpl.
    rproper.
  - unfold cut_var.
    remember (rename_var θ v) as x.
    dependent destruction x.
    + unfold denote_app,denote_abs,lift ; simpl.
      rproper.
    + unfold denote_app,denote_abs,lift ; simpl.
      unfold denote_var ; simpl.
      rproper.
  - remember (ConsRenaming (TailVar HeadVar) (trans_renaming exchange_renaming (weaken_renaming θ))) as θ'.
    specialize (IHf _ θ' (push_term e)).
    simpl in IHf.
    unfold denote_app at 1.
    rproper.
    eapply transitivity.
    2: apply IHf.
    2: LibReflexivity.
    simpl.
    pose (z1:=ConsEnv x0 (ConsEnv (denote_strong ^e r∙ x) x)).
    pose (z2:=ConsEnv (denote_strong ^(push_term e) r∙ ConsEnv y0 y) (ConsEnv y0 y)).
    (* this will be a lot of work *)
    Abort.
*)
    

Definition id {τ} : term (τ ⇒ τ) := tλ x → x.
Definition compose {τ₁ τ₂ τ₃} : term ((τ₂ ⇒ τ₃) ⇒ (τ₁ ⇒ τ₂) ⇒ (τ₁ ⇒ τ₃)) := tλ g f x → g ∙ (f ∙ x).

Definition compose_id_left : forall τ₁ τ₂ (f:term (τ₁ ⇒ τ₂)), (compose ∙ id ∙ f) ≃ f.
Proof.
  intros.
  unfold id,compose.
  unfold eqv,Eqv_instance_1.
  unfold denote_strong.
  Opaque lookup.
  simpl.
Abort.

(*

(***** substitution primitives *****)

Fixpoint weaken_substitution {Γ₁ Γ₂ τ} (θ:Γ₁ ≼ Γ₂) : Γ₁ ≼ τ∷Γ₂ :=
  match θ with
  | NullSubstitution _ => NullSubstitution
  | ConsSubstitution _ _ _ e θ' => ConsSubstitution (push_term e) (weaken_substitution θ')
  end.
Fixpoint identity_substitution {Γ} : Γ ≼ Γ :=
  match Γ with
  | nil => NullSubstitution
  | τ∷_ => ConsSubstitution (Var HeadVar) (weaken_substitution identity_substitution)
  end.
Definition cons_substitution {Γ₁ Γ₂ τ} (θ:Γ₁ ≼ Γ₂) : τ∷Γ₁ ≼ τ∷Γ₂ := 
  ConsSubstitution (Var HeadVar) (weaken_substitution θ).

(***** substitution applications *****)

Fixpoint substitute_var {Γ₁ Γ₂ τ} (θ:Γ₁ ≼ Γ₂) (x:τ ∈ Γ₁) : Γ₂ ⊢ τ :=
  match x in τ ∈ Γ₁
  return Γ₁ ≼ Γ₂ -> Γ₂ ⊢ τ
  with
  | HeadVar Γ₁' τ₁ => fun (θ:τ₁∷Γ₁' ≼ Γ₂) => 
      match θ with ConsSubstitution _ _ _ Γeτ _ => Γeτ end
  | TailVar Γ₁' τ₁ τ₂ x' => fun (θ:τ₁∷Γ₁' ≼ Γ₂) => 
      match θ in Γ₁ ≼ Γ₂
      return
        match Γ₁ with
        | nil => unit
        | τ₁∷Γ₁' => τ₂ ∈ Γ₁' -> Γ₂ ⊢ τ₂
        end
      with
        | NullSubstitution _ => tt
        | ConsSubstitution Γ₁' _ _ _ θ' => fun (x':τ₂ ∈ Γ₁') => 
            substitute_var θ' x'
      end x'
  end θ.

Fixpoint substitute_term {Γ₁ Γ₂ τ} (θ:Γ₁ ≼ Γ₂) (e:Γ₁ ⊢ τ) : Γ₂ ⊢ τ :=
  match e in Γ₁ ⊢ τ return Γ₁ ≼ Γ₂ -> Γ₂ ⊢ τ with
  | Val _ _ v => fun _ => Val v
  | Var Γ₁ _ x => fun (θ:Γ₁ ≼ Γ₂) => substitute_var θ x
  | Abs Γ₁ _ _ e => fun (θ:Γ₁ ≼ Γ₂) => Abs (substitute_term (cons_substitution θ) e)
  | App Γ₁ _ _ e₁ e₂ => fun (θ:Γ₁ ≼ Γ₂) => App (substitute_term θ e₁) (substitute_term θ e₂)
  end θ.

*)