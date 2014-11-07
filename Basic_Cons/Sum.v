Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.


Set Primitive Projections.

Set Universe Polymorphism.

Class Sum (C : Category) (c d p : Obj) : Type :=
{
  Inj_1 : Hom c p;
  Inj_2 : Hom d p;

  Sum_morph_ex : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), Hom p p';

  Sum_morph_com_1 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_1 = r1 ;
  
  Sum_morph_com_2 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_2 = r2;
  
  Sum_morph_unique : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p') (f g : Hom p p'), (f ∘ Inj_1 = r1) → (f ∘ Inj_2 = r2) → (g ∘ Inj_1 = r1) → (g ∘ Inj_2 = r2) → f = g
}.

Theorem Sum_iso {C : Category} (c d p p': Obj) : Sum C c d p -> Sum C c d p' -> p ≡ p'.
Proof.
  intros [S1 S2 SX SXC1 SXC2 SU] [S1' S2' SX' SXC1' SXC2' SU'].
  exists (SX p' S1' S2'); exists (SX' p S1 S2);
  [apply (SU p S1 S2)| apply (SU' p' S1' S2')]; trivial;
  rewrite assoc; repeat (rewrite SXC1 || rewrite SXC2 || rewrite SXC1' || rewrite SXC2'); trivial.
Qed.

Program Instance Sum_Functor {C : Category}
        (sm : Obj → Obj → Obj)
        (sm_sum : ∀ a b, Sum C a b (sm a b))
: Functor (Prod_Cat C C) C :=
{
  FO := fun x => sm (fst x) (snd x); 
  FA := fun a b f => @Sum_morph_ex C _ _ _ (sm_sum _ _) _ ((@Inj_1 C _ _ _ (sm_sum _ _)) ∘ (fst f)) ((@Inj_2 C _ _ _ (sm_sum _ _)) ∘ (snd f))
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

Class Has_Sums (C : Category) : Type :=
{
  HS_sum : Obj → Obj → Obj;

  HS_sum_sum : forall a b, Sum C a b (HS_sum a b);

  Sum_of := Sum_Functor HS_sum HS_sum_sum
}.

Existing Instance HS_sum_sum.






