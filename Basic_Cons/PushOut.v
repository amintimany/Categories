Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Section PushOut.
  Context {C : Category} {a b x : Obj} (f : Hom x a) (g : Hom x b).

  Class PushOut : Type :=
    {
      pushout : C;
      
      pushout_morph_1 : Hom a pushout;

      pushout_morph_2 : Hom b pushout;

      pushout_morph_com : pushout_morph_1 ∘ f = pushout_morph_2 ∘ g;

      pushout_morph_ex (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') : pm1 ∘ f = pm2 ∘ g → Hom pushout p';

      pushout_morph_ex_com_1 (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') (pmc : pm1 ∘ f = pm2 ∘ g) :
        (pushout_morph_ex p' pm1 pm2 pmc) ∘ pushout_morph_1 = pm1;

      pushout_morph_ex_com_2 (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p') (pmc : pm1 ∘ f = pm2 ∘ g) :
        (pushout_morph_ex p' pm1 pm2 pmc) ∘ pushout_morph_2 = pm2;

      pushout_morph_unique
        (p' : Obj) (pm1 : Hom a p') (pm2 : Hom b p')
        (pmc : pm1 ∘ f = pm2 ∘ g) (u u' : Hom pushout p') :
        u ∘ pushout_morph_1 = pm1 →
        u ∘ pushout_morph_2 = pm2 →
        u' ∘ pushout_morph_1 = pm1 →
        u' ∘ pushout_morph_2 = pm2 → u = u'
    }.

  Coercion pushout : PushOut >-> Obj.

  Theorem PushOut_iso (p1 p2 : PushOut) : p1 ≡ p2.
  Proof.
    apply (@Build_Isomorphism _ _ _ (pushout_morph_ex p2 pushout_morph_1 pushout_morph_2 pushout_morph_com) (pushout_morph_ex p1 pushout_morph_1 pushout_morph_2 pushout_morph_com)); eapply pushout_morph_unique;
    match goal with
        | [|- id ∘ _ = _] => simpl_ids; trivial
        | _ => idtac
    end; try apply pushout_morph_com;
    rewrite assoc; repeat (rewrite pushout_morph_ex_com_1 || rewrite pushout_morph_ex_com_2); trivial.
  Qed.

End PushOut.

Class Has_PushOuts (C : Category) : Type := has_pushouts : ∀ {a b c : C} (f : Hom a b) (g : Hom a c), PushOut f g.
