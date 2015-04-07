Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.CCC.

Require Import NatTrans.NatTrans.
Require Import Yoneda.Yoneda.

Section Init_Prod.

  Context {C : Category} {C_CCC : CCC C} {init : Initial C}.

  Program Instance Init_Prod_lr a : NatTrans (((CoYoneda C) _o) ((Prod_Func C) _o (@terminal _ init, a))) (((CoYoneda C) _o) init) :=
  {
    Trans := fun b f => @t_morph _ init b
  }.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    apply t_morph_unique.
  Qed.

  Next Obligation. (* Trans_com *)
  Proof.
    symmetry.
    apply Init_Prod_lr_obligation_1.
  Qed.

  Program Instance Init_Prod_rl a : NatTrans (((CoYoneda C) _o) init) (((CoYoneda C) _o) ((Prod_Func C) _o (@terminal _ init, a))) :=
{
  Trans := fun c g => compose C (Pi_1 (CCC_HC C init a)) (t_morph init c)
}.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    simpl_ids.
    rewrite <- assoc.
    apply f_equal.
    apply (t_morph_unique init).
  Qed.

  Next Obligation. (* Trans_com *)
  Proof.
    symmetry.
    apply Init_Prod_rl_obligation_1.
  Qed.
  
  Theorem Init_Prod a : ((Prod_Func C) _o (@terminal _ init, a)) ≡ init.
  Proof.
    apply (@CoIso (C^op)).
    CoYoneda.
    apply (NatIso _ _ (Init_Prod_lr a) (Init_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      apply (t_morph_unique init).
    }
    {
      intros c.
      eapply functional_extensionality; intros g; simpl; simpl_ids.
      match goal with
          [|- ?A = ?B] =>
          erewrite <- uncurry_curry with (f := A); erewrite <- uncurry_curry with (f := B)
      end.
      apply f_equal.
      apply (t_morph_unique init).
    }
  Qed.

End Init_Prod.
