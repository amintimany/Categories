Require Import Category.Main.

Section CoEqualizer.
  Context `(C : Category Obj Hom) {a b : Obj} (f g : Hom a b).

  Class CoEqualizer (ce : Obj) : Type :=
    {
      coequalizer_morph : Hom b ce;

      coequalizer_morph_com : coequalizer_morph ∘ f = coequalizer_morph ∘ g;

      coequalizer_morph_ex (ce' : Obj) (eqm : Hom b ce') : eqm ∘ f = eqm ∘ g → Hom ce ce';

      coequalizer_morph_ex_com (ce' : Obj) (eqm : Hom b ce') (eqmc : eqm ∘ f = eqm ∘ g) :
        (coequalizer_morph_ex ce' eqm eqmc) ∘ coequalizer_morph = eqm;

      coequalizer_morph_unique (ce' : Obj) (eqm : Hom b ce') (com : eqm ∘ f = eqm ∘ g) (u u' : Hom ce ce') : u ∘ coequalizer_morph = eqm → u' ∘ coequalizer_morph = eqm → u = u'
    }.

  Theorem CoEqualizer_iso (ce1 ce2 : Obj) : CoEqualizer ce1 → CoEqualizer ce2 → ce1 ≡ ce2.
  Proof.
    intros [ceqm ceqmc ceqmex ceqmec ceqmu] [ceqm' ceqmc' ceqmex' ceqmec' ceqmu'].
    exists (ceqmex ce2 ceqm' ceqmc'); exists (ceqmex' ce1 ceqm ceqmc); [eapply ceqmu | eapply ceqmu']; eauto 1.
    rewrite assoc; rewrite ceqmec; rewrite ceqmec'; trivial.
    rewrite assoc; rewrite ceqmec'; rewrite ceqmec; trivial.
  Qed.

End CoEqualizer.

Class Has_CoEqualizers `(C : Category Obj Hom) : Type :=
{
  CoEqualizer_of : ∀ {a b : Obj}, Hom a b → Hom a b → Obj;
  
  CoEqualizer_of_CoEqualizer : ∀ (a b : Obj) (f g : Hom a b), CoEqualizer C f g (CoEqualizer_of f g)
}.

Existing Instance CoEqualizer_of_CoEqualizer.
