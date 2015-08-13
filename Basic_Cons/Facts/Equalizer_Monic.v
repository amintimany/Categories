Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.

Require Import Basic_Cons.Equalizer.

Section Equalizer_Monic.
  Context {C : Category} {a b} (f g : (a –≻ b)%morphism) {e : Equalizer f g}.

  Program Definition Equalizer_Monic : (e ≫–> a)%morphism :=
    {|
      mono_morphism := equalizer_morph e
    |}.

  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    match goal with
        [H : ?A = ?B :> (c –≻ a)%morphism |- _] =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        cut (f ∘ A = g ∘ A)%morphism;
          [intros H1;
            cut (f ∘ B = g ∘ B)%morphism;
            [intros H2 | do 2 rewrite <- assoc; rewrite equalizer_morph_com; trivial
          ]| do 2 rewrite <- assoc; rewrite equalizer_morph_com; trivial
          ]
    end.
    eapply equalizer_morph_unique; eauto.
  Qed.

End Equalizer_Monic.
