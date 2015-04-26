Require Import Category.Main.
Require Import Functor.Functor Functor.Const_Func Functor.Functor_Ops.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.Operations NatTrans.Func_Cat.
Require Import Archetypal.Discr.
Require Import Limits.Limit Limits.Pointwise.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.GenProd.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).

(*
  This file shows that if a category is complete, then for any pair of objects x and y, we have
  (Arrow C) (Hom C x y) is isomorphic to Hom C x (Limit_of (Discr_Func Arr_y)).
  This of course would be a contradiction as soon as we have some objects c and d for which
  (Hom C c d) has more than one element.
  In other words, any complete category is a preorder category!!!

  The proof is precisely the proof that is given in Awodey's book "Category Theory" to show that
  any small and complete category is a preorder category. In deed, the constraints on universe
  variables generated by this proof, restricts C such that the level of its objects is less than or
  equal to the level of its arrows (Remember that in this development smallness and largeness is
  relative to universe levels).
*)

Section Complete_Preorder.
  Context (C : Category) (CC : Complete C) (x y : C).

  Local Definition Arr_y := (fun w : (Arrow C) => y).
  
  Local Definition LimOf_Arr_y := (Limit_of (Discr_Func Arr_y)).

  Local Definition GenProd_of_const_Hom_x_y := Type_Cat_GenProd _ ((FCOMP (Discr_Func Arr_y) (@Fix_Bi_Func_1 C^op _ _ x (Hom_Func.Hom_Func C))) _o).

  Local Program Definition Func_Iso : (Discr_Func ((Functor_compose (Discr_Func Arr_y) (@Fix_Bi_Func_1 C^op _ _ x (Hom_Func.Hom_Func C))) _o)) ≡≡ (Functor_compose (Discr_Func Arr_y) (@Fix_Bi_Func_1 C^op _ _ x (Hom_Func.Hom_Func C))) ::> Func_Cat _ _ :=
    {|
      iso_morphism := {|Trans := fun c h => h|};
      inverse_morphism := {|Trans := fun c h => h|}
    |}.

  Local Definition Local_Right_KanExt_Iso_Limits_Pointwise_LimOf_Arr_y__ISO__GenProd_of_const_Hom_x_y : Local_Right_KanExt_Iso Func_Iso (Limits_Pointwise _ x LimOf_Arr_y) ≡≡ GenProd_of_const_Hom_x_y ::> LoKan_Cone_Cat _ _ := Local_Right_KanExt_unique _ _ _ _.
  
  Local Definition Hom_x_LimOf_Arr_y_ISO_Arrow_C_to_Hom_x_y : (Hom x ((LimOf_Arr_y _o) tt)) ≡≡ (Arrow C → Hom x y) ::> Type_Cat :=
    LoKan_Cone_Iso_object_Iso _ _ Local_Right_KanExt_Iso_Limits_Pointwise_LimOf_Arr_y__ISO__GenProd_of_const_Hom_x_y tt.

End Complete_Preorder.