Require Import Category.Core.

(* General Product *)

Section General_Prod.
  Context `(C : Category Obj Hom) (A : Type) (objs : A → Obj).

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

Class Has_General_Products `(C : Category Obj Hom) (A : Type) : Type :=
{
  HGP_prod : (A → Obj) → Obj;

  HGP_prod_prod : ∀ (objs : A → Obj), General_Product C A objs (HGP_prod objs)
}.

Existing Instance HGP_prod_prod.

Notation Gen_Prod_of objs := (HGP_prod objs).




