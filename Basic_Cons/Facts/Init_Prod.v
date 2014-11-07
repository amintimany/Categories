Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.Initial.
Require Import Basic_Cons.CCC.

Require Import NatTrans.NatTrans.
Require Import Yoneda.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Section Init_Prod.

  Context {C : Category} {C_CCC : CCC C} {C_HI : Has_Initial C}.

  Program Instance Init_Prod_lr a : NatTrans (((Yoneda_emb C^op) _o) (Prod_of _o (Init_of C, a))) (((Yoneda_emb C^op) _o) (Init_of C)) :=
  {
    Trans := fun b f => i_morph b
  }.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    apply i_morph_unique.
  Qed.

  Program Instance Init_Prod_rl a : NatTrans (((Yoneda_emb C^op) _o) (Init_of C)) (((Yoneda_emb C^op) _o) (Prod_of _o (Init_of C, a))) :=
{
  Trans := fun c _ => ((i_morph c) ∘ Pi_1)
}.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    rewrite <- assoc.
    apply f_equal.
    apply i_morph_unique.
  Qed.

  Theorem Init_Prod a : (Prod_of _o (Init_of C, a)) ≡ Init_of C.
  Proof.
    apply (@CoIso (C^op)).
    Yoneda.
    apply (NatIso _ _ (Init_Prod_lr a) (Init_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      rewrite id_unit_left.
      apply (@i_morph_unique _ (Init_of C) (Init_of_init)).
    }
    {
      intros c.
      eapply functional_extensionality; intros g; simpl; simpl_ids.
      match goal with
          [|- ?A = ?B] =>
          erewrite <- uncurry_curry with (f := A); erewrite <- uncurry_curry with (f := B)
      end.
      apply f_equal.
      apply i_morph_unique.
    }
  Qed.

End Init_Prod.
