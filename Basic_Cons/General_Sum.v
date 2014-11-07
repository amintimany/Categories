Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

(* General Sum *)

Section General_Sum.
  Context (C : Category) (A : Type) (objs : A → Obj).

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

Class Has_General_Sums (C : Category) (A : Type) : Type :=
{
  Gen_Sum_of : (A → Obj) → Obj;

  Gen_Sum_sum : ∀ (objs : A → Obj), General_Sum C A objs (Gen_Sum_of objs)
}.

Existing Instance Gen_Sum_sum.


Class Has_Restricted_General_Sums (C : Category) (P : Type → Prop) : Type :=
  {
    HRGS_HGS : ∀ (A : Type), P A → Has_General_Sums C A
  }.

Existing Instance HRGS_HGS.

Class Has_All_General_Sums (C : Category) : Type :=
  {
    HAGS_HGS : ∀ (A : Type), Has_General_Sums C A
  }.

Existing Instance HAGS_HGS.



