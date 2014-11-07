Require Import Category.Main.
Require Import Functor.Functor.
Require Import Categories.Discr.
Require Import Basic_Cons.General_Product.
Require Import Limits.Limit.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Set Primitive Projections.

Set Universe Polymorphism.

Section Gen_Prod_Limit.
  Context (C : Category) (A : Type) (objs : A → Obj)
          (l : Cone (Discrete_Functor C A objs))
          (l_lim : Limit (Discrete_Functor C A objs) l).

  Program Instance Cone_for_projs (prod : Obj) (projs : ∀ a, Hom prod (objs a)) : Cone (Discrete_Functor C A objs) :=
    {
      Cone_obj := prod;

      Cone_arrow := projs
    }.

  Program Instance Gen_Prod_as_Limit : General_Product C A objs (Cone_obj l) :=
    {
      GP_Proj := Cone_arrow l;
      GP_Prod_morph_ex := λ a H, Cone_Morph_arrow (@t_morph _ _ (Lim_term _) (Cone_for_projs a H))
    }.

  Next Obligation. (* GP_Prod_morph_com *)
  Proof.

    match goal with
        [x : Obj |- _] =>
        rewrite (@Cone_Morph_com _ _ (Discrete_Functor C A objs) _ _ (@t_morph (Cone_Cat _) _ _ (Cone_for_projs x _)))
    end.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    match goal with
        [x : Obj, H : ∀ _, _ ∘ ?f = _, H' : ∀ _, _ ∘ ?g = _|- ?f = ?g] =>
        let Hx := fresh "H" in
        cut ((Build_Cone_Morph _ (Cone_for_projs x _) l f H) = (Build_Cone_Morph _ (Cone_for_projs x _) l g H')); [intros Hx; apply (@f_equal _ _ (@Cone_Morph_arrow _ _ _ _ _) _ _ Hx)|]
    end.
    apply (@t_morph_unique _ _ l_lim).
  Qed.

End Gen_Prod_Limit.

Section Limit_Gen_Prod.
  Context (C : Category) (A : Type) (objs : A → Obj)
          (p : Obj) (GP : General_Product C A objs p).

  Section Cone_Morph_to_Lim_of_Prod.
    Context (cn : Cone (Discrete_Functor C A objs)).

    Hint Resolve GP_Prod_morph_com.

    Program Instance Cone_Morph_to_Lim_of_Prod : Cone_Morph _ cn (Cone_for_projs C A objs p (@GP_Proj _ _ _ _ GP)) :=
      {
        Cone_Morph_arrow := @GP_Prod_morph_ex C A objs _ GP (Cone_obj cn) (Cone_arrow cn)
      }.

  End Cone_Morph_to_Lim_of_Prod.

  Program Instance Limit_of_Gen_Prod : Limit (Discrete_Functor C A objs) (Cone_for_projs C A objs p (@GP_Proj _ _ _ _ GP)) :=
    {
      Lim_term :=
        {|
          t_morph := λ d, Cone_Morph_to_Lim_of_Prod d
        |}
    }.

  Next Obligation.
    apply Cone_Morph_eq_simplify; destruct f; destruct g.
    eapply GP_Prod_morph_unique; eauto.
  Qed.

End Limit_Gen_Prod.

Section Has_Lim_Has_Gen_Prod.
  Context (C : Category) (A : Type) {HL : ∀ objs, Has_Limit (Discrete_Functor C A objs)}.

  Program Instance Has_Lim_Has_Gen_Prod : Has_General_Products C A :=
    {
      Gen_Prod_of := λ objs, Cone_obj (@HL_Limit _ _ _ (HL objs));
      Gen_Prod_prod := λ objs, Gen_Prod_as_Limit C A objs _ _
    }.

End Has_Lim_Has_Gen_Prod.


Section Has_Restr_Lim_Has_Restr_Gen_Prod.
  Context (C : Category) (A : Type) (P : Card_Restriction) {HRL : Has_Restricted_Limits C P}.

  Instance Has_Restr_Lim_Has_Restr_Gen_Prod : Has_Restricted_General_Products C P :=
    {
      HRGP_HGP := λ A PA,
                  {|
                    Gen_Prod_of := λ objs, Cone_obj (Restricted_Limit_of (Discrete_Functor C A objs) PA (Card_Rest_Respect _ _ (Discr_Hom_Iso A) PA));
                    Gen_Prod_prod := λ objs, Gen_Prod_as_Limit C A objs _ _
                  |}
    }.

End Has_Restr_Lim_Has_Restr_Gen_Prod.

Section Complete_Has_All_Gen_Prod.
  Context (C : Category) {HRL : Complete C}.

  Instance Complete_Has_All_Gen_Prod : Has_All_General_Products C :=
    {
      HAGP_HGP := λ A,
                  {|
                    Gen_Prod_of := λ objs, Cone_obj (Limit_of (Discrete_Functor C A objs));
                    Gen_Prod_prod := λ objs, Gen_Prod_as_Limit C A objs _ _
                  |}
    }.

End Complete_Has_All_Gen_Prod.

