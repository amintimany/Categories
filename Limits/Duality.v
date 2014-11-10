Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Ext_Cons.Arrow.


Require Import Limits.Limit.
Require Import Limits.CoLimit.

Set Primitive Projections.

Set Universe Polymorphism.

Section Cone_CoCone.
  Context {J C : Category} {D : Functor J C} (cn : Cone D).

  Program Instance CoCone_of_Cone : CoCone (Opposite_Functor D) :=
    {
      CoCone_obj := Cone_obj cn;

      CoCone_arrow := Cone_arrow cn;
      
      CoCone_com := λ _ _ h, Cone_com cn h
    }.

End Cone_CoCone.

Section CoCone_Cone.
  Context {J C : Category} {D : Functor J C} (ccn : CoCone D).

  Program Instance Cone_of_CoCone : Cone (Opposite_Functor D) :=
    {
      Cone_obj := CoCone_obj ccn;

      Cone_arrow := CoCone_arrow ccn;
      
      Cone_com := λ _ _ h, CoCone_com ccn h
    }.

End CoCone_Cone.

Section Cone_Morph_CoCone_Morph.
  Context {J C : Category} {D : Functor J C} {cn cn' : Cone D} (h : Cone_Morph D cn cn').

  Program Instance CoCone_Morph_of_Cone_Morph : CoCone_Morph (Opposite_Functor D) (CoCone_of_Cone cn') (CoCone_of_Cone cn) :=
    {
      CoCone_Morph_arrow := Cone_Morph_arrow h;

      CoCone_Morph_com := Cone_Morph_com h
    }.

End Cone_Morph_CoCone_Morph.

Section CoCone_Morph_Cone_Morph.
  Context {J C : Category} {D : Functor J C} {cn cn' : CoCone D} (h : CoCone_Morph D cn cn').

  Program Instance Cone_Morph_of_CoCone_Morph : Cone_Morph (Opposite_Functor D) (Cone_of_CoCone cn') (Cone_of_CoCone cn) :=
    {
      Cone_Morph_arrow := CoCone_Morph_arrow h;

      Cone_Morph_com := CoCone_Morph_com h
    }.

End CoCone_Morph_Cone_Morph.

Section Limit_CoLimit.
  Context {J C : Category}
          (D : Functor J C) (cn : Cone D)
          (L : Limit D cn).

  Program Instance CoLimit_of_Limit : CoLimit (Opposite_Functor D) (CoCone_of_Cone cn) :=
    {
      CoLim_init :=
        {| 
          i_morph := 
            λ d, CoCone_Morph_of_Cone_Morph (@t_morph _ _ (@Lim_term _ _ _ _ L) (Cone_of_CoCone d));
          i_morph_unique := _
        |}
    }.

  Next Obligation. (* i_morph_unique *)
    cut (Cone_Morph_of_CoCone_Morph f = Cone_Morph_of_CoCone_Morph g).
    + let H := fresh "H" in
      intros H;
        apply CoCone_Morph_eq_simplify;
        eapply f_equal with (f := Cone_Morph_arrow) in H;
        trivial.
      + apply (@t_morph_unique _ _ (@Lim_term _ _ _ _ L)).
  Qed.

End Limit_CoLimit.

Section CoLimit_Limit.
  Context {J C : Category}
          (D : Functor J C) (cn : CoCone D)
          (L : CoLimit D cn).

  Program Instance Limit_of_CoLimit : Limit (Opposite_Functor D) (Cone_of_CoCone cn) :=
    {
      Lim_term :=
        {|
          t_morph := λ d, Cone_Morph_of_CoCone_Morph (@i_morph _ _ (@CoLim_init _ _ _ _ L) (CoCone_of_Cone d));
          t_morph_unique := _
        |}
    }.

  Next Obligation. (* t_morph_unique *)
    cut (CoCone_Morph_of_Cone_Morph f = CoCone_Morph_of_Cone_Morph g).
    + let H := fresh "H" in
      intros H;
        apply Cone_Morph_eq_simplify;
        eapply f_equal with (f := CoCone_Morph_arrow) in H;
        trivial.
    + apply (@i_morph_unique _ _ (@CoLim_init _ _ _ _ L)).
  Qed.

End CoLimit_Limit.

Section Has_Restricted_Limits_CoLimits.
  Context {C : Category} (P : Card_Restriction)
  {HRL : Has_Restricted_Limits C P}.

  Program Instance Has_Restricted_Limits_CoLimits : Has_Restricted_CoLimits (C ^op) P :=
    {
      Restricted_CoLimit_of := 
        λ J D (PO : P Obj) (PA : P (Arrow _)),
        CoCone_of_Cone (Restricted_Limit_of (Opposite_Functor D) PO (Card_Rest_Respect _ _ (Arrow_OP_Iso _) PA))
    }.

  Next Obligation.
    apply (CoLimit_of_Limit (Opposite_Functor D)).
    apply Restricted_Limit_of_Limit.
  Qed.

End Has_Restricted_Limits_CoLimits.

Section Has_Restricted_CoLimits_Limits.
  Context {C : Category} (P : Card_Restriction)
  {HRCL : Has_Restricted_CoLimits C P}.

  Program Instance Has_Restricted_CoLimits_Limits : Has_Restricted_Limits (C ^op) P :=
    {
      Restricted_Limit_of := 
        λ J D (PO : P Obj) (PA : P (Arrow _)),
        Cone_of_CoCone (Restricted_CoLimit_of (Opposite_Functor D) PO (Card_Rest_Respect _ _ (Arrow_OP_Iso _) PA))
    }.

  Next Obligation.
    apply (Limit_of_CoLimit (Opposite_Functor D)).
    apply Restricted_CoLimit_of_CoLimit.
  Qed.

End Has_Restricted_CoLimits_Limits.

Section Complete_CoComplete.
  Context {C : Category} {CC : Complete C}.

  Instance Complete_CoComplete : CoComplete (C ^op).
  Proof.
    eapply (@No_Restriction_CoComplete (C ^op) (Build_Card_Restriction (λ _, True) (λ _ _ _ _ , I))); auto.
    eapply Complete_Has_Restricted_Limits in CC.
    eapply Has_Restricted_Limits_CoLimits.
    eauto 1.
    simpl; trivial.
  Qed.

End Complete_CoComplete.

Section CoComplete_Complete.
  Context {C : Category} {CC : CoComplete C}.

  Instance CoComplete_Complete : Complete (C ^op).
  Proof.
    eapply (@No_Restriction_Complete (C ^op) (Build_Card_Restriction (λ _, True) (λ _ _ _ _ , I))); auto.
    eapply CoComplete_Has_Restricted_CoLimits in CC.
    eapply Has_Restricted_CoLimits_Limits.
    eauto 1.
    simpl; trivial.
  Qed.

End CoComplete_Complete.
