Require Import Category.Main.
Require Import Functor.Functor.
Require Import Categories.Discr.
Require Import Basic_Cons.General_Sum.
Require Import Limits.CoLimit.
Require Import Basic_Cons.Initial.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Section Gen_Sum_CoLimit.
  Context `(C : Category Obj Hom) (A : Type) (objs : A → Obj)
          (l : CoCone (Discrete_Functor C A objs))
          (l_clim : CoLimit (Discrete_Functor C A objs) l).

  Program Instance CoCone_for_injs (sum : Obj) (injs : ∀ a, Hom (objs a) sum) : CoCone (Discrete_Functor C A objs) :=
    {|
      CoCone_obj := sum;

      CoCone_arrow := injs
    |}.

  Program Instance Gen_Sum_as_CoLimit : General_Sum C A objs (CoCone_obj l) :=
    {
      GS_Inj := CoCone_arrow l;
      GS_Sum_morph_ex := λ a H, CoCone_Morph_arrow (@i_morph _ _ _ _ (CoLim_init _) (CoCone_for_injs a H))
    }.

  Next Obligation. (* GP_Prod_morph_com *)
  Proof.
    match goal with
        [x : Obj |- _] =>
        rewrite (@CoCone_Morph_com _ _ _ _ _ _ (Discrete_Functor C A objs) _ _ (@i_morph _ _ _ _ _ (CoCone_for_injs x _)))
    end.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    match goal with
        [x : Obj, H : ∀ _, f ∘ _ = _, H' : ∀ _, g ∘ _ = _|- ?f = ?g] =>
        let H := fresh "H" in
        cut ((Build_CoCone_Morph _ l (CoCone_for_injs x _) f H) = (Build_CoCone_Morph _ l (CoCone_for_injs x _) g H')); [intros H; dependent destruction H; trivial|]
    end.
    apply (@i_morph_unique _ _ _ _ l_clim).
  Qed.

End Gen_Sum_CoLimit.

Section CoLimit_Gen_Sum.
  Context `(C : Category Obj Hom) (A : Type) (objs : A → Obj)
          (s : Obj) (GS : General_Sum C A objs s).

  Section CoCone_Morph_from_CoLim_of_Sum.
    Context (cn : CoCone (Discrete_Functor C A objs)).

    Hint Resolve GS_Sum_morph_com.

    Program Instance CoCone_Morph_from_CoLim_of_Sum : CoCone_Morph _ (CoCone_for_injs C A objs s (@GS_Inj _ _ _ _ _ _ GS)) cn :=
      {
        CoCone_Morph_arrow := @GS_Sum_morph_ex _ _ C A objs _ GS (CoCone_obj cn) (CoCone_arrow cn)
      }.

  End CoCone_Morph_from_CoLim_of_Sum.

  Program Instance Limit_of_Gen_Prod : CoLimit (Discrete_Functor C A objs) (CoCone_for_injs C A objs s (@GS_Inj _ _ _ _ _ _ GS)) :=
    {
      CoLim_init :=
        {|
          i_morph := λ d, CoCone_Morph_from_CoLim_of_Sum d
        |}
    }.

  Next Obligation.
    apply CoCone_Morph_eq_simplify; destruct f; destruct g.
    eapply GS_Sum_morph_unique; eauto.
  Qed.

End CoLimit_Gen_Sum.

Section Has_CoLim_Has_Gen_Sum.
  Context `(C : Category Obj Hom) (A : Type) {HCL : ∀ objs, Has_CoLimit (Discrete_Functor C A objs)}.

  Program Instance Has_Lim_Has_Gen_Prod : Has_General_Sums C A :=
    {
      Gen_Sum_of := λ objs, CoCone_obj (@HCL_CoLim _ _ _ _ _ _ _ (HCL objs));
      Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit C A objs _ _
    }.

End Has_CoLim_Has_Gen_Sum.


Section Has_Restr_CoLim_Has_Restr_Gen_Sum.
  Context `(C : Category Obj Hom) (A : Type) (P : Card_Restriction) {HRCL : Has_Restricted_CoLimits C P}.

  Instance Has_Restr_CoLim_Has_Restr_Gen_Sum : Has_Restricted_General_Sums C P :=
    {
      HRGS_HGS := λ A PA,
                  {|
                    Gen_Sum_of := λ objs, CoCone_obj (Restricted_CoLimit_of (Discrete_Functor C A objs) PA (Card_Rest_Respect _ _ (Discr_Hom_Iso A) PA));
                    Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit C A objs _ _
                  |}
    }.

End Has_Restr_CoLim_Has_Restr_Gen_Sum.

Section CoComplete_Has_All_Gen_Sum.
  Context `(C : Category Obj Hom) {CC : CoComplete C}.

  Instance CoComplete_Has_All_Gen_Sums : Has_All_General_Sums C :=
    {
      HAGS_HGS := λ A,
                  {|
                    Gen_Sum_of := λ objs, CoCone_obj (CoLimit_of (Discrete_Functor C A objs));
                    Gen_Sum_sum := λ objs, Gen_Sum_as_CoLimit C A objs _ _
                  |}
    }.

End CoComplete_Has_All_Gen_Sum.


