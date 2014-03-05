Require Import FP.Core.

Class Galois (A B:qtype) :=
  { galoisβ : dom (A ⇒ B)
  ; galoisα : dom (B ⇒ A)
  ; galois_idL : (galoisβ ⊙ galoisα) ⊑ id
  ; galois_idR : id ⊑ (galoisα ⊙ galoisβ)
  }.

Instance : forall A B `{! Galois A B }, Galois (A ⇒ A) (B ⇒ B) :=
  { galoisβ := λ f → galoisβ ⊙ f ⊙ galoisα
  ; galoisα := λ g → galoisα ⊙ g ⊙ galoisβ
  }. admit. admit.
Defined.

Class CGalois (A B:qtype) := 
  { cgalois : dom A -> dom B -> Prop
    (*       b'
           /R  \⊑
          a'    b 
           \⊑  /R
             a
    *)
  ; cgalois_upper : forall (a a':dom A) (b:dom B),
      cgalois a b -> a' ⊑ a -> cgalois a' b
  ; cgalois_lower : forall (a:dom A) (b b':dom B),
      cgalois a b -> b ⊑ b' -> cgalois a b'
  }.

Class CGaloisComplete A B `{! CGalois A B } :=
  { cgalois_completeβ : dom (A ⇒ B)
  ; cgalois_completeα : dom (B ⇒ A)
  ; cgalois_completeβ₁ : forall a, cgalois a (cgalois_completeβ ∙ a)
  ; cgalois_completeβ₂ : forall a b, cgalois a b -> a ⊑ cgalois_completeα ∙ b
  ; cgalois_completeα₁ : forall b, cgalois (cgalois_completeα ∙ b) b
  ; cgalois_completeα₂ : forall a b, cgalois a b -> cgalois_completeβ ∙ a ⊑ b
  }.

Instance : forall A B `{! CGalois A B }, CGalois (A ⇒ A) (B ⇒ B) :=
  { cgalois := fun af bf =>
      forall a b, cgalois a b -> cgalois (af ∙ a) (bf ∙ b)
  }.
Proof.
  - intros.
    simpl ; simpl in H ; intros.
    apply (cgalois_upper (a ∙ a0) (a' ∙ a0) (b ∙ b0)) ; qproper_elim ; qproper.
    apply H ; auto.
  - intros.
    simpl ; simpl in H ; intros.
    apply (cgalois_lower (a ∙ a0) (b ∙ b0) (b' ∙ b0)) ; qproper_elim ; qproper.
    apply H ; auto.
Defined.

Section Correspondance.
  Context {A B} `{! CGalois A B ,! CGaloisComplete A B }.
  
  Local Instance : Galois A B :=
    { galoisβ := cgalois_completeβ
    ; galoisα := cgalois_completeα
    }.
  Proof.
    - apply qmonotonic_intro ; unfold "⇉" ; intros.
      change (cgalois_completeβ ∙ (cgalois_completeα ∙ x) ⊑ y).
      Transitivity (cgalois_completeβ ∙ (cgalois_completeα ∙ y)) ; [qproper_elim ; qproper|].
      clear H.
      apply cgalois_completeα₂.
      apply cgalois_completeα₁.
    - apply qmonotonic_intro ; unfold "⇉" ; intros.
      change (x ⊑ cgalois_completeα ∙ (cgalois_completeβ ∙ y)).
      Transitivity (cgalois_completeα ∙ (cgalois_completeβ ∙ x)) ; [|qproper_elim ; qproper].
      clear H.
      apply cgalois_completeβ₂.
      apply cgalois_completeβ₁.
  Defined.
End Correspondance.