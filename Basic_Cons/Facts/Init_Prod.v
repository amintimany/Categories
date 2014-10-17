Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.Initial.
Require Import Basic_Cons.CCC.

Require Import NatTrans.NatTrans.
Require Import Yoneda.Main.

Section Init_Prod.

  Context `{C : Category Obj Hom} {C_CCC : CCC C} {C_HI : Has_Initial C}.

  Program Instance Init_Prod_lr (a : Obj) : NatTrans (((CoYoneda_emb C) _o) (_I_ C × a)) (((CoYoneda_emb C) _o) _I_ C) :=
  {
    Trans := fun b f => i_morph b
  }.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    apply i_morph_unique.
  Qed.


  Program Instance Init_Prod_rl (a : Obj) : NatTrans (((CoYoneda_emb C) _o) _I_ C) (((CoYoneda_emb C) _o) (_I_ C × a)) :=
{
  Trans := fun c _ => ((i_morph c) ∘ Pi_1)
}.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    rewrite <- assoc.
    f_equal.
    apply i_morph_unique.
  Qed.

  Theorem Init_Prod (a : Obj) : (_I_ C × a) ≡ _I_ C.
  Proof.
    CoYoneda.
    apply (NatIso _ _ (Init_Prod_lr a) (Init_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      rewrite id_unit_left.
      apply (@i_morph_unique _ _ _ (_I_ C) (HI_init_init)).
    }
    {
      intros c.
      eapply functional_extensionality; intros g; simpl.
      erewrite id_unit_left.
      match goal with
          [|- ?A = ?B] =>
          erewrite <- uncurry_curry with (f := A); erewrite <- uncurry_curry with (f := B)
      end.
      apply f_equal.
      apply i_morph_unique.
    }
  Qed.

End Init_Prod.
