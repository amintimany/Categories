Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

(* General Product *)

Section General_Prod.
  Context (C : Category) (A : Type) (objs : A → Obj).

  Class General_Product (GP_Prod : Obj) : Type :=
    {
      GP_Proj : ∀ (a : A), Hom GP_Prod (objs a);
      
      GP_Prod_morph_ex : ∀ (p' : Obj) (prj : ∀ (a : A), Hom p' (objs a)), Hom p' GP_Prod;

      GP_Prod_morph_com : ∀ (p' : Obj) (prj : ∀ (a : A), Hom p' (objs a)),
                            ∀ (a : A), (GP_Proj a) ∘ (GP_Prod_morph_ex p' prj) = (prj a);
      
      GP_Prod_morph_unique : ∀ (p' : Obj) (prj : ∀ (a : A), Hom p' (objs a)) (f g : Hom p' GP_Prod),
                               (∀ (a : A), (GP_Proj a) ∘ f = (prj a)) → (∀ (a : A), (GP_Proj a) ∘ g = (prj a)) →
                               f = g
    }.

  Context (p p' : Obj).

  Theorem General_Product_iso : General_Product p → General_Product p' → p ≡ p'.
  Proof.
    intros [PRJ PX PXC PU] [PRJ' PX' PXC' PU'].
    exists (PX' p PRJ); exists (PX p' PRJ');
    [apply (PU p PRJ) | apply (PU' p' PRJ')]; eauto 2;
      intros a; rewrite <- assoc; repeat (rewrite PXC || rewrite PXC'); trivial.
Qed.

End General_Prod.

(* Product_Functor defined *)

Class Has_General_Products (C : Category) (A : Type) : Type :=
{
  Gen_Prod_of : (A → Obj) → Obj;

  Gen_Prod_prod : ∀ (objs : A → Obj), General_Product C A objs (Gen_Prod_of objs)
}.

Existing Instance Gen_Prod_prod.

Class Has_Restricted_General_Products (C : Category) (P : Type → Prop) : Type :=
  {
    HRGP_HGP : ∀ (A : Type), P A → Has_General_Products C A
  }.

Existing Instance HRGP_HGP.

Class Has_All_General_Products (C : Category) : Type :=
  {
    HAGP_HGP : ∀ (A : Type), Has_General_Products C A
  }.

Existing Instance HAGP_HGP.
