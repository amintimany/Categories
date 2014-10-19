Require Import Category.Main.
Require Import Functor.Main.
Require Import Categories.Discr.
Require Import Basic_Cons.General_Sum.
Require Import Limits.Limit.
Require Import Limits.CoLimit.
Require Import Limits.Duality.
Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Ext_Cons.Arrow.

Section Gen_Sum_CoLimit.
  Context `(C : Category Obj Hom) (A : Type) (objs : A → Obj)
          (l : CoCone (Opposite_Functor (Discrete_Functor C A objs)))
          (l_clim : CoLimit (Opposite_Functor (Discrete_Functor C A objs)) l).

  Program Let Cone_for_injs (sum : Obj) (injs : ∀ a, Hom sum (objs a)) : Cone (Discrete_Functor C A objs) :=
    {|
      Cone_obj := sum;

      Cone_arrow := injs
    |}.

  Program Let CoCone_for_injs (sum : Obj) (injs : ∀ a, Hom sum (objs a)) : CoCone (Opposite_Functor (Discrete_Functor C A objs)) :=
    {|
      CoCone_obj := sum;

      CoCone_arrow := injs
    |}.

  Program Instance Gen_Sum_as_CoLimit_op : General_Sum C ^op A objs (CoCone_obj l) :=
    {
      GS_Inj := CoCone_arrow l;
      GS_Sum_morph_ex := λ a H, CoCone_Morph_arrow (@i_morph _ _ _ _ (CoLim_init _) (CoCone_for_injs a H))
    }.

  Next Obligation. (* GP_Prod_morph_com *)
  Proof.
    match goal with
        [x : Obj |- _] =>
        match goal with
            [y : ∀ _, Hom x _ |- _] => 
            apply (@CoCone_Morph_com _ _ _ _ _ _ (Opposite_Functor (Discrete_Functor C A objs)) l _ (@i_morph _ _ (CoCone_Cat _) _ (CoLim_init _) (CoCone_for_injs x y)))
        end
    end.
  Qed.

  Next Obligation.
  Proof.
    match goal with
        [x : Obj |- _] =>
        match goal with
            [y : ∀ _, Hom x _ |- _] => 
            match goal with
                [H : ∀ _, _ ∘ ?f = _, H' : ∀ _, _ ∘ ?g = _|- ?f = ?g] =>
                let U := fresh "H" in
                cut (((Build_Cone_Morph (Opposite_Functor (Opposite_Functor (Discrete_Functor C A objs))) (Cone_of_CoCone (CoCone_of_Cone (Cone_for_injs p' inj))) (Cone_of_CoCone l) f H)) = ((Build_Cone_Morph (Opposite_Functor (Opposite_Functor (Discrete_Functor C A objs))) (Cone_of_CoCone (CoCone_of_Cone (Cone_for_injs p' inj))) (Cone_of_CoCone l) g H'))); [intros U; dependent destruction U; trivial|]
            end
        end
    end.
    apply (@t_morph_unique _ _ _ _ (Limit_of_CoLimit _ _ l_clim)).
  Qed.

End Gen_Sum_CoLimit.

Section Has_CoLim_Has_Gen_Sum_op.
  Context `(C : Category Obj Hom) (A : Type) {HCL : ∀ objs, Has_CoLimit (Opposite_Functor (Discrete_Functor C A objs))}.

  Program Instance Has_CoLim_Has_Gen_Sum_op : Has_General_Sums C ^op A :=
    {
      Gen_Sum_of := λ objs, CoCone_obj (@HCL_CoLim _ _ _ _ _ _ _ (HCL objs));
      Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit_op C A objs _ _
    }.

End Has_CoLim_Has_Gen_Sum_op.


Section Has_Restr_CoLim_Has_Restr_Gen_Sum_op.
  Context `(C : Category Obj Hom) (A : Type) (P : Card_Restriction) {HRCL : Has_Restricted_CoLimits C ^op P}.

  Program Instance Has_Restr_CoLim_Has_Restr_Gen_Sum_op : Has_Restricted_General_Sums C ^op P :=
    {
      HRGS_HGS := λ A PA,
                  {|
                    Gen_Sum_of := λ objs, CoCone_obj (@Restricted_CoLimit_of _ _ _ _ HRCL _ _ _ (Opposite_Functor (Discrete_Functor C A objs)) PA (Card_Rest_Respect _ _ (Isomorphic_trans _ _ _ (Discr_Hom_Iso A) (Arrow_OP_Iso (Discr_Cat A))) PA));
                    Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit_op C A objs _ _
                  |}
    }.

End Has_Restr_CoLim_Has_Restr_Gen_Sum_op.

Section CoComplete_Has_All_Gen_Sums_op.
  Context `(C : Category Obj Hom) {HRL : CoComplete C ^op}.

  Instance CoComplete_Has_All_Gen_Sums_op : Has_All_General_Sums C ^op :=
    {
      HAGS_HGS := λ A,
                  {|
                    Gen_Sum_of := λ objs, CoCone_obj (CoLimit_of (Opposite_Functor (Discrete_Functor C A objs)));
                    Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit_op C A objs _ _
                  |}
    }.

End CoComplete_Has_All_Gen_Sums_op.

Section Has_Restr_CoLim_Has_Restr_Gen_Sum.
  Context `(C : Category Obj Hom) (A : Type) (P : Card_Restriction) {HRCL : Has_Restricted_CoLimits C P}.

  Instance Has_Restr_CoLim_Has_Restr_Gen_Sum : Has_Restricted_General_Sums C P.
  Proof.
    assert (H := Has_Restr_CoLim_Has_Restr_Gen_Sum_op C ^op).
    destruct C.
    apply H; trivial.
  Defined.

End Has_Restr_CoLim_Has_Restr_Gen_Sum.

Section CoComplete_Has_All_Gen_Sums.
  Context `(C : Category Obj Hom) {HRL : CoComplete C}.

  Instance CoComplete_Has_All_Gen_Sum : Has_All_General_Sums C.
  Proof.
    assert (H := @CoComplete_Has_All_Gen_Sums_op _ _ C ^op).
    destruct C.
    apply H; trivial.
  Defined.

End CoComplete_Has_All_Gen_Sums.

