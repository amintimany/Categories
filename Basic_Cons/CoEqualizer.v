Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Section CoEqualizer.
  Context {C : Category} {a b : Obj} (f g : Hom a b).

  Class CoEqualizer : Type :=
    {
      coequalizer : C;

      coequalizer_morph : Hom b coequalizer;

      coequalizer_morph_com : coequalizer_morph ∘ f = coequalizer_morph ∘ g;

      coequalizer_morph_ex (ce' : Obj) (eqm : Hom b ce') : eqm ∘ f = eqm ∘ g → Hom coequalizer ce';

      coequalizer_morph_ex_com (ce' : Obj) (eqm : Hom b ce') (eqmc : eqm ∘ f = eqm ∘ g) :
        (coequalizer_morph_ex ce' eqm eqmc) ∘ coequalizer_morph = eqm;

      coequalizer_morph_unique (ce' : Obj) (eqm : Hom b ce') (com : eqm ∘ f = eqm ∘ g) (u u' : Hom coequalizer ce') : u ∘ coequalizer_morph = eqm → u' ∘ coequalizer_morph = eqm → u = u'
    }.

  Coercion coequalizer : CoEqualizer >-> Obj.

  Theorem CoEqualizer_iso (ce1 ce2 : CoEqualizer) : ce1 ≡ ce2.
  Proof.
    eapply (@Build_Isomorphism _ _ _ (coequalizer_morph_ex ce2 coequalizer_morph coequalizer_morph_com) (coequalizer_morph_ex ce1 coequalizer_morph coequalizer_morph_com)); eapply coequalizer_morph_unique; [| | simpl_ids; trivial| | | simpl_ids; trivial]; try apply coequalizer_morph_com.
    rewrite assoc; repeat rewrite coequalizer_morph_ex_com; trivial.
    rewrite assoc; repeat rewrite coequalizer_morph_ex_com; trivial.
  Qed.

End CoEqualizer.

Class Has_CoEqualizers (C : Category) : Type := has_coequalizers : ∀ (a b : C) (f g : Hom a b), CoEqualizer f g.
