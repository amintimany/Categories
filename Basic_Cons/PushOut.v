Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Section PushOut.
  Context (C : Category) {a b x : Obj} (f : Hom x a) (g : Hom x b).

  Class PushOut (p : Obj) : Type :=
    {
      pushout_morph_1 : Hom a p;

      pushout_morph_2 : Hom b p;

      pushout_morph_com : pushout_morph_1 ∘ f = pushout_morph_2 ∘ g;

      pushout_morph_ex (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') : pm1 ∘ f = pm2 ∘ g → Hom p p';

      pushout_morph_ex_com_1 (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') (pmc : pm1 ∘ f = pm2 ∘ g) :
        (pushout_morph_ex p' pm1 pm2 pmc) ∘ pushout_morph_1 = pm1;

      pushout_morph_ex_com_2 (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') (pmc : pm1 ∘ f = pm2 ∘ g) :
        (pushout_morph_ex p' pm1 pm2 pmc) ∘ pushout_morph_2 = pm2;

      pushout_morph_unique
        (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p')
        (pmc : pm1 ∘ f = pm2 ∘ g) (u u' : Hom p p') :
        u ∘ pushout_morph_1 = pm1 →
        u ∘ pushout_morph_2 = pm2 →
        u' ∘ pushout_morph_1 = pm1 →
        u' ∘ pushout_morph_2 = pm2 → u = u'
    }.

  Theorem PushOut_iso (p1 p2 : Obj) : PushOut p1 → PushOut p2 → p1 ≡ p2.
  Proof.
    intros [pm1 pm2 pmc pmex pmec1 pmec2 pmu] [pm1' pm2' pmc' pmex' pmec1' pmec2' pmu'].
    exists (pmex p2 pm1' pm2' pmc'); exists (pmex' p1 pm1 pm2 pmc); [eapply pmu | eapply pmu']; eauto 1;
    rewrite assoc; repeat (rewrite pmec1 || rewrite pmec1' || rewrite pmec2 || rewrite pmec2'); trivial.
  Qed.

End PushOut.

Class Has_PushOuts (C : Category) : Type :=
{
  PushOut_of : ∀ {a b x : Obj}, Hom x a → Hom x b → Obj;

  PushOut_of_PushOut : ∀ (a b x : Obj) (f : Hom x a) (g : Hom x b), PushOut C f g (PushOut_of f g)
}.

Existing Instance PushOut_of_PushOut.
