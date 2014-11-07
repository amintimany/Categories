Require Import Category.Main.
Require Import Basic_Cons.General_Product.
Require Import Basic_Cons.General_Sum.

Set Primitive Projections.

Set Universe Polymorphism.

Section Gen_Sum_Gen_Prod.
  Context (C : Category) (A : Type) (objs : A → Obj) (p : Obj) (GP : General_Product C A objs p).

  Program Instance Gen_Sum_of_Gen_Prod : General_Sum (C ^op) A objs p :=
    {
      GS_Inj := @GP_Proj _ _ _ _ GP;

      GS_Sum_morph_ex := λ a H, @GP_Prod_morph_ex _ _ _ _ GP a H;
      
      GS_Sum_morph_com := λ a H b, @GP_Prod_morph_com _ _ _ _ GP a H b;

      GS_Sum_morph_unique := λ a H f g, @GP_Prod_morph_unique _ _ _ _ GP a H f g
    }.

End Gen_Sum_Gen_Prod.

Section Has_Gen_Sum_op_Has_Gen_Prod.
  Context (C : Category) (A : Type) (HGP : Has_General_Products C A).

  Program Instance Has_Gen_Prod_op_Has_Gen_Sum : Has_General_Sums (C^op) A :=
    {
      Gen_Sum_of := @Gen_Prod_of C A _;
      Gen_Sum_sum := λ a, Gen_Sum_of_Gen_Prod _ _ _ _ (@Gen_Prod_prod C A _ a)
    }.

End Has_Gen_Sum_op_Has_Gen_Prod.

Section Has_Restr_Gen_Sum_op_Has_Restr_Gen_Prod.
  Context (C : Category) (P : Type → Prop) (HGP : Has_Restricted_General_Products C P).

  Program Instance Has_Restr_Gen_Sum_op_Has_Restr_Gen_Prod : Has_Restricted_General_Sums (C ^op) P :=
    {
      HRGS_HGS := λ A PA, Has_Gen_Prod_op_Has_Gen_Sum _ _ (HRGP_HGP A PA)
    }.

End Has_Restr_Gen_Sum_op_Has_Restr_Gen_Prod.

Section Has_All_Gen_Sum_op_Has_All_Gen_Prod.
  Context (C : Category) (HGP : Has_All_General_Products C).

  Program Instance Has_All_Gen_Sum_op_Has_All_Gen_Prod : Has_All_General_Sums (C ^op) :=
    {
      HAGS_HGS := λ A, Has_Gen_Prod_op_Has_Gen_Sum _ _ (HAGP_HGP A)
    }.

End Has_All_Gen_Sum_op_Has_All_Gen_Prod.

Section Prod_Sum.
  Context (C : Category) (A : Type) (objs : A → Obj) (s : Obj) (GS : General_Sum C A objs s).

  Program Instance Gen_Prod_of_Gen_Sum : General_Product (C ^op) A objs s :=
    {
      GP_Proj := @GS_Inj _ _ _ _ GS;

      GP_Prod_morph_ex := λ a H, @GS_Sum_morph_ex _ _ _ _ GS a H;
      
      GP_Prod_morph_com := λ a H b, @GS_Sum_morph_com _ _ _ _ GS a H b;

      GP_Prod_morph_unique := λ a H f g, @GS_Sum_morph_unique _ _ _ _ GS a H f g
    }.

End Prod_Sum.


Section Has_Gen_Prod_op_Has_Gen_Sum.
  Context (C : Category) (A : Type) (HGP : Has_General_Sums C A).

  Program Instance Has_Gen_Sum_op_Has_Gen_Prod : Has_General_Products (C ^op) A :=
    {
      Gen_Prod_of := @Gen_Sum_of C A _;
      Gen_Prod_prod := λ a, Gen_Prod_of_Gen_Sum _ _ _ _ (@Gen_Sum_sum C A _ a)
    }.

End Has_Gen_Prod_op_Has_Gen_Sum.

Section Has_Restr_Gen_Prod_op_Has_Restr_Gen_Sum.
  Context (C : Category) (P : Type → Prop) (HGP : Has_Restricted_General_Sums C P).

  Program Instance Has_Restr_Gen_Prod_op_Has_Restr_Gen_Sum : Has_Restricted_General_Products (C ^op) P :=
    {
      HRGP_HGP := λ A PA, Has_Gen_Sum_op_Has_Gen_Prod _ _ (HRGS_HGS A PA)
    }.

End Has_Restr_Gen_Prod_op_Has_Restr_Gen_Sum.

Section Has_All_Gen_Prod_op_Has_All_Gen_Sum.
  Context (C : Category) (HGP : Has_All_General_Sums C).

  Program Instance Has_All_Gen_Prod_op_Has_All_Gen_Sum : Has_All_General_Products (C ^op) :=
    {
      HAGP_HGP := λ A, Has_Gen_Sum_op_Has_Gen_Prod _ _ (HAGS_HGS A)
    }.

End Has_All_Gen_Prod_op_Has_All_Gen_Sum.

