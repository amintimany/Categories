Require Import Category.Core.

Section Equalizer.
  Context `(C : Category Obj Hom) {a b : Obj} (f g : Hom a b).

  Class Equalizer (e : Obj) : Type :=
    {
      equalizer_morph : Hom e a;

      equalizer_morph_com : f ∘ equalizer_morph = g ∘ equalizer_morph;

      equalizer_morph_ex (e' : Obj) (eqm : Hom e' a) : f ∘ eqm = g ∘ eqm → Hom e' e;

      equalizer_morph_ex_com (e' : Obj) (eqm : Hom e' a) (eqmc : f ∘ eqm = g ∘ eqm) :
        equalizer_morph ∘ (equalizer_morph_ex e' eqm eqmc) = eqm;

      equalizer_morph_unique (e' : Obj) (eqm : Hom e' a) (com : f ∘ eqm = g ∘ eqm) (u u' : Hom e' e) : equalizer_morph ∘ u = eqm → equalizer_morph ∘ u' = eqm → u = u'
    }.

  Theorem Equalizer_iso (e1 e2 : Obj) : Equalizer e1 → Equalizer e2 → e1 ≡ e2.
  Proof.
    intros [eqm eqmc eqmex eqmec eqmu] [eqm' eqmc' eqmex' eqmec' eqmu'].
    exists (eqmex' e1 eqm eqmc); exists (eqmex e2 eqm' eqmc'); [eapply eqmu | eapply eqmu']; eauto 1.
    rewrite <- assoc; rewrite eqmec; rewrite eqmec'; trivial.
    rewrite <- assoc; rewrite eqmec'; rewrite eqmec; trivial.
  Qed.

End Equalizer.

Class Has_Equalizers `(C : Category Obj Hom) : Type :=
{
  HE_Eqz : ∀ {a b : Obj},  Hom a b → Hom a b → Obj;
  
  HE_Eqz_Equalizer : ∀ (a b : Obj) (f g : Hom a b), Equalizer C f g (HE_Eqz f g)
}.

Existing Instance HE_Eqz_Equalizer.

Notation Equalizer_of f g := (HE_Eqz f g).


