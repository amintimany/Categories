Require Import Category.Main.
Require Import Functor.Main.
Require Import Ext_Cons.Arrow.
Require Import Basic_Cons.General_Product.
Require Import Basic_Cons.Equalizer.
Require Import Basic_Cons.General_Sum.
Require Import Basic_Cons.CoEqualizer.
Require Import Basic_Cons.Facts.Gen_Prod_Sum_Duality.
Require Import Basic_Cons.Facts.Equalizer_CoEqualizer_Duality.
Require Import Basic_Cons.Facts.Gen_Prod_Iso.
Require Import Limits.Duality.
Require Import Limits.Gen_Prod_Eq_Limits.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Limits.Limit.
Require Import Limits.CoLimit.

Set Primitive Projections.

Set Universe Polymorphism.

Section Gen_Sum_CoEq_Co_Complete.
   Context `{C : Category Obj Hom} `{J : Category Obj' Hom'} {HGPO : Has_General_Sums C Obj'} {HGPH : Has_General_Sums C (Arrow J)} {HE : Has_CoEqualizers C} (D : Functor J C).

   Program Definition CoLim_CoCone : CoCone D.
   Proof.
     set (U := CoCone_of_Cone (@Lim_Cone _ _ (C ^op) _ _ _ (Has_Gen_Sum_op_Has_Gen_Prod _ _ HGPO) (Has_Gen_Prod_Iso _ _ (Arrow (J ^op)) (Has_Gen_Sum_op_Has_Gen_Prod _ _ HGPH) (Isomorphic_sym _ _ (Arrow_OP_Iso J))) (@Has_CoEqualizer_op_Has_Equalizer _ _ _ HE) (Opposite_Functor D))).
     rewrite (Functor_Opposite_Opposite D) in U.
     destruct C.
     destruct J.
     exact U.
   Defined.

   Program Let CoLim_CoCone_is_CoLimit_op_op : CoLimit (Opposite_Functor (Opposite_Functor D)) (CoCone_of_Cone (@Lim_Cone _ _ (C ^op) _ _ _ (Has_Gen_Sum_op_Has_Gen_Prod _ _ HGPO) (Has_Gen_Prod_Iso _ _ (Arrow (J ^op)) (Has_Gen_Sum_op_Has_Gen_Prod _ _ HGPH) (Isomorphic_sym _ _ (Arrow_OP_Iso J))) (@Has_CoEqualizer_op_Has_Equalizer _ _ _ HE) (Opposite_Functor D))).
   Proof.
     apply CoLimit_of_Limit.
     apply Lim_Cone_is_Limit.
   Qed.

   Program Definition CoLim_CoCone_is_CoLimit : CoLimit D CoLim_CoCone.
   Proof.
     assert (U := CoLim_CoCone_is_CoLimit_op_op).
     unfold CoLim_CoCone.
     rewrite (Opposite_Opposite_Functor D).
     destruct C.
     destruct J.
     simpl in *.
     trivial.
   Qed.     

   Opaque CoLim_CoCone.

End Gen_Sum_CoEq_Co_Complete.


Section Restricted_CoLimits.
  Context `{C : Category Obj Hom} (P : Card_Restriction) {CHRP : Has_Restricted_General_Sums C P} {HE : Has_CoEqualizers C}.

  Program Instance Restr_Gen_Sum_Eq_Restr_CoLimits : Has_Restricted_CoLimits C P :=
    {
      Restricted_CoLimit_of := λ _ _ J D PO PH, @CoLim_CoCone _ _ _ _ _ _ (HRGS_HGS _ PO) (HRGS_HGS _ PH) _ D;
      Restricted_CoLimit_of_CoLimit := λ _ _ J D PO PH, @CoLim_CoCone_is_CoLimit _ _ _ _ _ _ (HRGS_HGS _ PO) (HRGS_HGS _ PH) _ D
    }.

End Restricted_CoLimits.

Section CoComplete.
  Context `{C : Category Obj Hom} {CHAP : Has_All_General_Sums C} {HE : Has_CoEqualizers C}.
  
  Program Instance Gen_Sums_CoEq_CoComplete : CoComplete C :=
    {
        CoLimit_of := λ _ _ _ D, @CoLim_CoCone _ _ _ _ _ _ (HAGS_HGS _) (HAGS_HGS _) _ D;
        CoLimit_of_CoLimit := λ _ _ _ D, @CoLim_CoCone_is_CoLimit _ _ _ _ _ _ (HAGS_HGS _) (HAGS_HGS _) _ D
    }.
  
End CoComplete.
