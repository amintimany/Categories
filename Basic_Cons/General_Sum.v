Require Import Category.Core.

(* General Sum *)

Section General_Sum.
  Context `(C : Category Obj Hom) (A : Type) (objs : A → Obj).

  Class General_Sum (GS_Sum : Obj) : Type :=
    {
      GS_Inj : ∀ (a : A), Hom (objs a) GS_Sum;
      
      GS_Sum_morph_ex : ∀ (p' : Obj) (inj : ∀ (a : A), Hom (objs a) p'), Hom GS_Sum p';

      GS_Sum_morph_com : ∀ (p' : Obj) (inj : ∀ (a : A), Hom (objs a) p'),
                            ∀ (a : A), (GS_Sum_morph_ex p' inj) ∘ (GS_Inj a) = (inj a);
      
      GS_Sum_morph_unique : ∀ (p' : Obj) (inj : ∀ (a : A), Hom (objs a) p') (f g : Hom GS_Sum p'),
                               (∀ (a : A), f ∘ (GS_Inj a) = (inj a)) → (∀ (a : A), g ∘ (GS_Inj a) = (inj a)) →
                               f = g
    }.

  Context (p p' : Obj).

  Theorem General_Sum_iso : General_Sum p → General_Sum p' → p ≡ p'.
  Proof.
    intros [SIJ SX SXC SU] [SIJ' SX' SXC' SU'].
    exists (SX p' SIJ'); exists (SX' p SIJ);
    [apply (SU p SIJ) | apply (SU' p' SIJ')]; eauto 2;
      intros a; rewrite assoc; repeat (rewrite SXC || rewrite SXC'); trivial.
Qed.

End General_Sum.

(* Product_Functor defined *)

Class Has_General_Sums `(C : Category Obj Hom) (A : Type) : Type :=
{
  HGS_sum : (A → Obj) → Obj;

  HGS_sum_sum : ∀ (objs : A → Obj), General_Sum C A objs (HGS_sum objs)
}.

Existing Instance HGS_sum_sum.

Notation Gen_Sum_of objs := (HGS_sum objs).




