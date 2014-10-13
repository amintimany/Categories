Require Import Category.Core.

Section PullBack.
  Context `(C : Category Obj Hom) {a b x : Obj} (f : Hom a x) (g : Hom b x).
  
  Class PullBack (p : Obj) : Type :=
    {
      pullback_morph_1 : Hom p a;

      pullback_morph_2 : Hom p b;

      pullback_morph_com : f ∘ pullback_morph_1 = g ∘ pullback_morph_2;

      pullback_morph_ex (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) : f ∘ pm1 = g ∘ pm2 → Hom p' p;

      pullback_morph_ex_com_1 (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) (pmc : f ∘ pm1 = g ∘ pm2) :
        pullback_morph_1 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm1;

      pullback_morph_ex_com_2 (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) (pmc : f ∘ pm1 = g ∘ pm2) :
        pullback_morph_2 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm2;

      pullback_morph_unique
        (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b)
        (pmc : f ∘ pm1 = g ∘ pm2) (u u' : Hom p' p) :
        pullback_morph_1 ∘ u = pm1 →
        pullback_morph_2 ∘ u = pm2 →
        pullback_morph_1 ∘ u' = pm1 →
        pullback_morph_2 ∘ u' = pm2 → u = u'
    }.

  Theorem PullBack_iso (p1 p2 : Obj) : PullBack p1 → PullBack p2 → p1 ≡ p2.
  Proof.
    intros [pm1 pm2 pmc pmex pmec1 pmec2 pmu] [pm1' pm2' pmc' pmex' pmec1' pmec2' pmu'].
    exists (pmex' p1 pm1 pm2 pmc); exists (pmex p2 pm1' pm2' pmc'); [eapply pmu | eapply pmu']; eauto 1;
    rewrite <- assoc; repeat (rewrite pmec1 || rewrite pmec1' || rewrite pmec2 || rewrite pmec2'); trivial.
  Qed.

End PullBack.

Class Has_PullBacks `(C : Category Obj Hom) : Type :=
{
  HPB_PB : ∀ {a b x : Obj}, Hom a x → Hom b x → Obj;

  HPB_PB_PullBack : ∀ (a b x : Obj) (f : Hom a x) (g : Hom b x), PullBack C f g (HPB_PB f g)
}.

Existing Instance HPB_PB_PullBack.

Notation PullBack_of f g := (HPB_PB f g).