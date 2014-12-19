Require Import Category.Main.

Require Import Basic_Cons.CoEqualizer.


Set Primitive Projections.

Set Universe Polymorphism.

Section CoEqualizer_Epic.
  Context {C : Category} {a b } (f g : Hom a b) {ce : CoEqualizer f g}.

  Program Instance CoEqualizer_Epic : b –≫ ce :=
    {
      epi_morphism := coequalizer_morph f g
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
