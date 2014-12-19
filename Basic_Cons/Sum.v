Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Class Sum {C : Category} (c d : C) : Type :=
{
  sum : C;

  Inj_1 : Hom c sum;

  Inj_2 : Hom d sum;

  Sum_morph_ex : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), Hom sum p';

  Sum_morph_com_1 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_1 = r1 ;
  
  Sum_morph_com_2 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_2 = r2;
  
  Sum_morph_unique : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p') (f g : Hom sum p'), (f ∘ Inj_1 = r1) → (f ∘ Inj_2 = r2) → (g ∘ Inj_1 = r1) → (g ∘ Inj_2 = r2) → f = g
}.

Coercion sum : Sum >-> Obj.

Theorem Sum_iso {C : Category} (c d : C) (S S' : Sum c d) : S ≡ S'.
Proof.
  eapply (@Build_Isomorphism _ _ _ (Sum_morph_ex S' Inj_1 Inj_2) (Sum_morph_ex S Inj_1 Inj_2));
    eapply Sum_morph_unique; trivial;
  rewrite assoc; repeat (rewrite Sum_morph_com_1 || rewrite Sum_morph_com_2); trivial.
Qed.

Class Has_Sums (C : Category) := has_sums : ∀ a b, Sum a b.

Program Instance Sum_Func {C : Category}
        (HS : Has_Sums C)
: Functor (Prod_Cat C C) C :=
{
  FO := fun x => HS (fst x) (snd x); 
  FA := fun a b f => Sum_morph_ex _ (Inj_1 ∘ (fst f)) (Inj_2 ∘ (snd f))
}.

Next Obligation. (* F_id *)  
Proof.
  eapply Sum_morph_unique.
  rewrite Sum_morph_com_1; reflexivity.
  rewrite Sum_morph_com_2; reflexivity.
  auto.
  auto.
Qed.

Next Obligation. (* F_compose *)  
Proof.
  eapply Sum_morph_unique.
  + rewrite Sum_morph_com_1; reflexivity.
  + rewrite Sum_morph_com_2; reflexivity.
  + match goal with
        [|- (_ ∘ ?A) ∘ ?B = _] =>
        let H := fresh "H" in
        reveal_comp A B
    end.
    rewrite Sum_morph_com_1.
    match goal with
        [|- ?A ∘ ?B ∘ _ = _] =>
        let H := fresh "H" in
        reveal_comp A B
    end.
    rewrite Sum_morph_com_1.  
    auto.
  + match goal with
        [|- (_ ∘ ?A) ∘ ?B = _] =>
        let H := fresh "H" in
        reveal_comp A B
    end.
    rewrite Sum_morph_com_2.
    match goal with
        [|- ?A ∘ ?B ∘ _ = _] =>
        let H := fresh "H" in
        reveal_comp A B
    end.
    rewrite Sum_morph_com_2.  
    auto.
Qed.

(* Sum_Functor defined *)






