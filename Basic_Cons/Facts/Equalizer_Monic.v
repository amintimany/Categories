Require Import Category.Main.

Require Import Basic_Cons.Equalizer.


Set Primitive Projections.

Set Universe Polymorphism.

Section Equalizer_Monic.
  Context `{C : Category Obj Hom} {a b e} (f g : Hom a b) {Eq : Equalizer C f g e}.

  Program Instance Equalizer_Monic : e ≫–> a :=
    {
      mono_morphism := equalizer_morph C f g
    }.

  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    match goal with
        [H : ?A = ?B :> Hom c a |- _] =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        cut (f ∘ A = g ∘ A);
          [intros H1;
            cut (f ∘ B = g ∘ B);
            [intros H2 | do 2 rewrite <- assoc; rewrite equalizer_morph_com; trivial
          ]| do 2 rewrite <- assoc; rewrite equalizer_morph_com; trivial
          ]
    end.
    eapply equalizer_morph_unique; eauto.
  Qed.

End Equalizer_Monic.
