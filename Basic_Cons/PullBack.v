Require Import Category.Main.

Section PullBack.
  Context {C : Category} {a b x : C} (f : Hom a x) (g : Hom b x).
  
  Class PullBack : Type :=
    {
      pullback : C;

      pullback_morph_1 : Hom pullback a;

      pullback_morph_2 : Hom pullback b;

      pullback_morph_com : f ∘ pullback_morph_1 = g ∘ pullback_morph_2;

      pullback_morph_ex (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) : f ∘ pm1 = g ∘ pm2 → Hom p' pullback;

      pullback_morph_ex_com_1 (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) (pmc : f ∘ pm1 = g ∘ pm2) :
        pullback_morph_1 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm1;

      pullback_morph_ex_com_2 (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b) (pmc : f ∘ pm1 = g ∘ pm2) :
        pullback_morph_2 ∘ (pullback_morph_ex p' pm1 pm2 pmc) = pm2;

      pullback_morph_ex_unique
        (p' : Obj) (pm1 : Hom p' a) (pm2 : Hom p' b)
        (pmc : f ∘ pm1 = g ∘ pm2) (u u' : Hom p' pullback) :
        pullback_morph_1 ∘ u = pm1 →
        pullback_morph_2 ∘ u = pm2 →
        pullback_morph_1 ∘ u' = pm1 →
        pullback_morph_2 ∘ u' = pm2 → u = u'
    }.

  Coercion pullback : PullBack >-> Obj.

  Theorem PullBack_iso (p1 p2 : PullBack) : p1 ≡ p2.
  Proof.
    apply (Build_Isomorphism _ _ _ (pullback_morph_ex p1 pullback_morph_1 pullback_morph_2 pullback_morph_com) (pullback_morph_ex p2 pullback_morph_1 pullback_morph_2 pullback_morph_com)); eapply pullback_morph_ex_unique;
    match goal with
      | [|- _ ∘ id = _] => simpl_ids; trivial
      | _ => idtac
    end; try apply pullback_morph_com;
    rewrite <- assoc; repeat (rewrite pullback_morph_ex_com_1 || rewrite pullback_morph_ex_com_2); trivial.
  Qed.

End PullBack.

Definition Has_PullBacks (C : Category) : Type := ∀ (a b c : C) (f : Hom a c) (g : Hom b c), PullBack f g.

Existing Class Has_PullBacks.

Arguments PullBack _ {_ _ _} _ _, {_ _ _ _} _ _.

Arguments pullback {_ _ _ _ _ _} _.
Arguments pullback_morph_1 {_ _ _ _ _ _} _.
Arguments pullback_morph_1 {_ _ _ _ _ _} _.
Arguments pullback_morph_com {_ _ _ _ _ _} _.
Arguments pullback_morph_ex {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_com_1 {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_com_2 {_ _ _ _ _ _} _ _ _ _ _.
Arguments pullback_morph_ex_unique {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.

(* PushOut is the dual of PullBack *)

Definition PushOut (C : Category) := @PullBack (C^op).

Existing Class PushOut.

Arguments PushOut _ {_ _ _} _ _, {_ _ _ _} _ _.

Definition Has_PushOuts (C : Category) : Type := ∀ (a b c : C) (f : Hom c a) (g : Hom c b), PushOut f g.

Existing Class Has_PushOuts.