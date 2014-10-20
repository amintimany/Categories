Require Import Category.Main.
Require Import Functor.Functor.
Require Import Basic_Cons.General_Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Section Gen_Prod_Iso.
  Context `(C : Category Obj Hom) (A B : Type) (objs : A → Obj) (p : Obj)
          (GP : General_Product C A objs p) (I : B ≡ A).

  Let equal_f : ∀ {A B : Type} {f g : A → B} (H : f = g) (x : A), f x = g x.
  Proof.
    intros ? ? ? ? H x; rewrite H; trivial.
  Defined.

  Program Instance Gen_Prod_Iso : General_Product C B (λ x, objs (@iso_morphism _ _ _ _ _ I x)) p :=
    {
      GP_Proj := λ x, GP_Proj _ _ _ (@iso_morphism _ _ _ _ _ I x);
      GP_Prod_morph_ex := 
        (λ (x : Obj) (prj : ∀ (y : B), Hom x (objs (@iso_morphism _ _ _ _ _ I y))), @GP_Prod_morph_ex _ _ _ _ _ _ GP _ (λ y, match (equal_f (@right_inverse _ _ _ _ _ _ (@iso_morphism_isomorphism _ _ _ _ _ I))) y in (_ = z) return Hom _ (objs z) with eq_refl => prj (@inverse_morphism _ _ _ _ _ _ (@iso_morphism_isomorphism _ _ _ _ _ I) y) end))
    }.

  Next Obligation. (* GP_Prod_morph_com *)
  Proof.
    destruct I as [If [Ir Iil Iir]]; clear I; cbv in Iir, Iil.
    rewrite (@GP_Prod_morph_com _ _ _ _ _ _ _ _ (λ y, match equal_f Iir y in (_ = z) return Hom p' (objs z) with eq_refl => prj (Ir y) end)).
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
        [Hf : ∀ a : B, GP_Proj _ _ _ _ ∘ ?f = ?prj a, Hg : ∀ a : B, GP_Proj _ _ _ _ ∘ ?g = ?prj a |- ?f = ?g] =>
        let x := fresh "x" in
        let Hf' := fresh "Hf'" in
        let Hg' := fresh "Hg'" in
        eapply (@GP_Prod_morph_unique _ _ _ _ _ _ _ _ (λ y, match equal_f Iir y in (_ = z) return Hom p' (objs z) with eq_refl => prj (Ir y) end)); 
          intros x; rewrite <- (equal_f Iir x)
    end; trivial.
  Qed.

End Gen_Prod_Iso.

Section Has_Gen_Prod_Iso.
  Context `(C : Category Obj Hom) (A B : Type)
          (GP : Has_General_Products C A) (I : B ≡ A).
  
  Program Instance Has_Gen_Prod_Iso : Has_General_Products C B :=
    {
      Gen_Prod_of := λ pr_of, Gen_Prod_of (λ y, pr_of (@inverse_morphism _ _ _ _ _ _ (@iso_morphism_isomorphism _ _ _ _ _ I) y))

    }.

  Next Obligation. (* Gen_Prod_prod *)
  Proof.
    assert (U := @Gen_Prod_Iso _ _ _ _ B _ _ (Gen_Prod_prod (λ y : A, objs (@inverse_morphism _ _ _ _ _ _ (@iso_morphism_isomorphism _ _ _ _ _ I) y))) I).
    destruct I as [If [Ir Iil Iir]]; clear I; cbv - [Gen_Prod_of] in *.
    cut (objs = (λ x : B, objs (Ir (If x)))).
    intros H.
    rewrite <- H in U.
    exact U.
    extensionality z.
    rewrite (equal_f Iil z); trivial.
  Qed.

End Has_Gen_Prod_Iso.






