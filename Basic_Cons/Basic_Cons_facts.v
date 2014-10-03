(*
   Facts about basic constructions.
*)

Require Import Category.Core.
Require Import Functor.Core.
Require Import Ext_Cons.Core.

Require Import Basic_Cons.Initial.
Require Import Basic_Cons.CCC.

Require Import NatTrans.NatTrans.
Require Import Yoneda.Yoneda.

Section Term_Prod.

  Context `{C : Category Obj Hom} {C_HT : Has_Terminal C} {C_HP : Has_Products C}.

  Program Instance Term_Prod_lr (a : Obj) : NatTrans (((Yoneda_emb C) _o) a × _T_ C) (((Yoneda_emb C) _o) a) :=
  {
    Trans := fun b f => Pi_1 ∘ f
  }.

  Program Instance Term_Prod_rl (a : Obj) : NatTrans (((Yoneda_emb C) _o) a) (((Yoneda_emb C) _o) a ×  _T_ C) :=
  {
    Trans := fun b f =>  Prod_morph_ex _ f (@T_morph _ _ _ _ b)
  }.

  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    eapply Prod_morph_unique.
    apply Prod_morph_com_1.
    apply Prod_morph_com_2.
    rewrite <- assoc.
    rewrite Prod_morph_com_1; trivial.
    rewrite <- assoc.
    rewrite Prod_morph_com_2.
    apply t_morph_unique.
  Qed.

  Theorem Term_Prod (a : Obj) : (a × _T_ C) ≡ a.
  Proof.
    Yoneda.
    apply (NatIso _ _ (Term_Prod_lr a) (Term_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      simpl_ids.
      apply Prod_morph_com_1.
    }
    {
      intros c.
      extensionality g; simpl.
      simpl_ids.
      eapply Prod_morph_unique.
      apply Prod_morph_com_1.
      apply Prod_morph_com_2.
      trivial.
      apply t_morph_unique.
    }
  Qed.

End Term_Prod.


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
