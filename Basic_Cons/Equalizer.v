Require Import Category.Main.

Section Equalizer.
  Context {C : Category} {a b : Obj} (f g : Hom a b).

  Class Equalizer : Type :=
    {
      equalizer : C;

      equalizer_morph : Hom equalizer a;

      equalizer_morph_com : f ∘ equalizer_morph = g ∘ equalizer_morph;

      equalizer_morph_ex (e' : Obj) (eqm : Hom e' a) : f ∘ eqm = g ∘ eqm → Hom e' equalizer;

      equalizer_morph_ex_com (e' : Obj) (eqm : Hom e' a) (eqmc : f ∘ eqm = g ∘ eqm) :
        equalizer_morph ∘ (equalizer_morph_ex e' eqm eqmc) = eqm;

      equalizer_morph_unique (e' : Obj) (eqm : Hom e' a) (com : f ∘ eqm = g ∘ eqm) (u u' : Hom e' equalizer) : equalizer_morph ∘ u = eqm → equalizer_morph ∘ u' = eqm → u = u'
    }.

  Coercion equalizer : Equalizer >-> Obj.

  Theorem Equalizer_iso (e1 e2 : Equalizer) : e1 ≡ e2.
  Proof.
    apply (Build_Isomorphism _ _ _ (equalizer_morph_ex e1 equalizer_morph equalizer_morph_com) ((equalizer_morph_ex e2 equalizer_morph equalizer_morph_com)));
    eapply equalizer_morph_unique; [| | simpl_ids; trivial| | |simpl_ids; trivial]; try apply equalizer_morph_com.
    rewrite <- assoc; repeat rewrite equalizer_morph_ex_com; auto.
    rewrite <- assoc; repeat rewrite equalizer_morph_ex_com; auto.
  Qed.

End Equalizer.

Arguments Equalizer _ {_ _} _ _, {_ _ _} _ _.

Definition Has_Equalizers (C : Category) : Type := ∀ (a b : C) (f g : Hom a b), Equalizer f g.

Existing Class Has_Equalizers.

(* CoEqualizer is the dual of equalzier *)

Definition CoEqualizer {C : Category} := @Equalizer C^op.

Arguments CoEqualizer _ {_ _} _ _, {_ _ _} _ _.

Existing Class CoEqualizer.

Definition Has_CoEqualizers (C : Category) : Type := ∀ (a b : C) (f g : Hom a b), CoEqualizer f g.

Existing Class Has_CoEqualizers.




