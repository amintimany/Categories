Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Terminal.
Require Import Basic_Cons.Product.

Require Import NatTrans.NatTrans.
Require Import Yoneda.Main.

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