Require Import Category.Core.

Require Import Basic_Cons.CoEqualizer.

Section CoEqualizer_Epic.
  Context `{C : Category Obj Hom} {a b e} (f g : Hom a b) {Eq : CoEqualizer C f g e}.

  Program Instance CoEqualizer_Epic : b –≫ e :=
    {
      epi_morphism := coequalizer_morph C f g
    }.

  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    match goal with
        [H : ?A = ?B :> Hom b c |- _] =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        cut (A ∘ f = A ∘ g);
          [intros H1;
            cut (B ∘ f = B ∘ g);
            [intros H2 | do 2 rewrite assoc; rewrite coequalizer_morph_com; trivial
          ]| do 2 rewrite assoc; rewrite coequalizer_morph_com; trivial
          ]
    end.
    eapply coequalizer_morph_unique; eauto.
  Qed.

End CoEqualizer_Epic.
