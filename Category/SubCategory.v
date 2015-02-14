Require Import Category.Category.

Section SubCategory.
  Context (C : Category)
          (Obj_Cri : Obj → Prop)
          (Hom_Cri : ∀ a b, Hom a b → Prop)
          (Hom_Cri_id : ∀ a, Obj_Cri a → Hom_Cri _ _ (@id _ a))
          (Hom_Cri_compose : ∀ a b c (f : Hom a b) (g : Hom b c),
                               Hom_Cri _ _ f → Hom_Cri _ _ g → Hom_Cri _ _ (g ∘ f)).

  Local Obligation Tactic := idtac.

  Program Instance SubCategory : Category :=
  {
    Obj := sig Obj_Cri;

    Hom := λ a b, sig (Hom_Cri (proj1_sig a) (proj1_sig b));

    compose := λ _ _ _ f g, exist _ ((proj1_sig g) ∘ (proj1_sig f))
                                  (Hom_Cri_compose _ _ _ (proj1_sig f) (proj1_sig g) (proj2_sig f) (proj2_sig g));

    id := λ a, exist _ (@id C (proj1_sig a)) (Hom_Cri_id (proj1_sig a) (proj2_sig a))
  }.

  Next Obligation.
    intros.
    apply sig_proof_irrelevance; simpl; abstract auto.
  Qed.

  Next Obligation.
    symmetry.
    apply SubCategory_obligation_1.
  Qed.

  Next Obligation.
    intros a b [ho hp].
    apply sig_proof_irrelevance.
    simpl; auto.
  Qed.
  
  Next Obligation.
    intros a b [ho hp].
    apply sig_proof_irrelevance.
    simpl; auto.
  Qed.

End SubCategory.

Notation Wide_SubCategory C Hom_Cri := (SubCategory C (λ _, True) Hom_Cri).

Notation Full_SubCategory C Obj_Cri := (SubCategory C Obj_Cri (λ _ _ _, True) (λ _ _, I) (λ _ _ _ _ _ _ _, I)).

