Require Import Category.Main.
Require Import Functor.Functor.
Require Import Basic_Cons.General_Sum.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Set Primitive Projections.

Set Universe Polymorphism.

Section Gen_Sum_Iso.
  Context (C : Category) (A B : Type) (objs : A → Obj) (p : Obj)
          (GP : General_Sum C A objs p) (I : @Isomorphic Type_Cat B A).

  Let equal_f : ∀ {A B : Type} {f g : A → B} (H : f = g) (x : A), f x = g x.
  Proof.
    intros ? ? ? ? H x; rewrite H; trivial.
  Defined.

  Program Instance Gen_Sum_Iso : General_Sum C B (λ x, objs (@iso_morphism _ _ _ I x)) p :=
    {
      GS_Inj := λ x, GS_Inj _ _ _ (@iso_morphism _ _ _ I x);
      GS_Sum_morph_ex := 
        (λ (x : Obj) (inj : ∀ (y : B), Hom (objs (@iso_morphism _ _ _ I y)) x), @GS_Sum_morph_ex _ _ _ _ GP _ (λ y, match (equal_f (@right_inverse _ _ _ _ (@iso_morphism_isomorphism _ _ _ I))) y in (_ = z) return Hom (objs z) _ with eq_refl => inj (@inverse_morphism _ _ _ _ (@iso_morphism_isomorphism _ _ _ I) y) end))
    }.

  Next Obligation. (* GP_Prod_morph_com *)
  Proof.
    destruct I as [If [Ir Iil Iir]]; clear I; cbv in Iir, Iil.
    rewrite (@GS_Sum_morph_com _ _ _ _ _ _ (λ y, match equal_f Iir y in (_ = z) return Hom (objs z) p' with eq_refl => inj (Ir y) end)).
    cbv.
    match goal with
        [|- ?A = ?B] =>
        let H := fresh "H" in
        cut (A ~= B); [intros H; rewrite H; trivial|]
    end.
    destruct (match
       match Iir in (_ = y) return (y = (λ x : A, If (Ir x))) with
       | eq_refl => eq_refl
       end in (_ = y) return (y (If a) = If a)
     with
     | eq_refl => eq_refl
     end).
    cbv.
    repeat rewrite (equal_f Iil a); trivial.
  Qed. 

  Next Obligation. (* GP_Prod_morph_unique *)
  Proof.
    destruct I as [If [Ir Iil Iir]]; clear I; cbv in Iir, Iil.
    match goal with
        [Hf : ∀ a : B, ?f ∘ GS_Inj _ _ _ _ = ?inj a, Hg : ∀ a : B, ?g ∘ GS_Inj _ _ _ _ = ?inj a |- ?f = ?g] =>
        let x := fresh "x" in
        let Hf' := fresh "Hf'" in
        let Hg' := fresh "Hg'" in
        eapply (@GS_Sum_morph_unique _ _ _ _ _ _ (λ y, match equal_f Iir y in (_ = z) return Hom (objs z) p' with eq_refl => inj (Ir y) end)); 
          intros x; rewrite <- (equal_f Iir x)
    end ; trivial.
  Qed.

End Gen_Sum_Iso.

Section Has_Gen_Sum_Iso.
  Context (C : Category) (A B : Type)
          (GP : Has_General_Sums C A) (I : @Isomorphic Type_Cat B A).
  
  Program Instance Has_Gen_Prod_Iso : Has_General_Sums C B :=
    {
      Gen_Sum_of := λ sm_of, Gen_Sum_of (λ y, sm_of (@inverse_morphism _ _ _ _ (@iso_morphism_isomorphism _ _ _ I) y))

    }.

  Next Obligation. (* Gen_Prod_prod *)
  Proof.
    assert (U := @Gen_Sum_Iso _ _ B _ _ (Gen_Sum_sum (λ y : A, objs (@inverse_morphism _ _ _ _ (@iso_morphism_isomorphism _ _ _ I) y))) I).
    destruct I as [If [Ir Iil Iir]]; clear I; cbv - [Gen_Sum_of] in *.
    simpl in *.
    cut (objs = (λ x : B, objs (Ir (If x)))).
    intros H.
    rewrite <- H in U.
    exact U.
    extensionality z.
    rewrite (equal_f Iil z); trivial.
  Qed.

End Has_Gen_Sum_Iso.






