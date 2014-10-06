Require Import Category.Core.

Class PullBack `(C : Category Obj Hom) {a b x : Obj} (f : Hom a x) (g : Hom b x) (p : Obj) : Type :=
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

Theorem PullBack_iso `{C : Category Obj Hom} {a b x : Obj} (f : Hom a x) (g : Hom b x) (p1 p2 : Obj) : PullBack C f g p1 → PullBack C f g p2 → p1 ≡ p2.
Proof.
  intros [pm1 pm2 pmc pmex pmec1 pmec2 pmu] [pm1' pm2' pmc' pmex' pmec1' pmec2' pmu'].
  exists (pmex' p1 pm1 pm2 pmc); exists (pmex p2 pm1' pm2' pmc'); [eapply pmu | eapply pmu']; eauto 1;
  rewrite <- assoc; repeat (rewrite pmec1 || rewrite pmec1' || rewrite pmec2 || rewrite pmec2'); trivial.
Qed.

