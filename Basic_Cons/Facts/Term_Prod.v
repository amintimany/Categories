Require Import Category.Main.
Require Import Functor.Main.

Require Import Basic_Cons.Terminal.
Require Import Basic_Cons.Product.

Require Import NatTrans.NatTrans NatTrans.NatIso.
Require Import Yoneda.Yoneda.

(** 1 × a ≡ a. where 1 is the terminal object. *)
Section Term_Prod.
  Context {C : Category} {term : Terminal C} {CHP : Has_Products C}.

  (** Natural transformations to be used with Yoneda. *)
  Program Definition Term_Prod_lr (a : C) :
    NatTrans
      ((Yoneda C) _o (CHP a term))%object
      ((Yoneda C) _o a)%object
    :=
      {|
        Trans := fun b f => @compose C _ _ _ f (@Pi_1 _ _ _ (CHP a term))
      |}.

  Program Definition Term_Prod_rl (a : Obj) :
    NatTrans
      ((Yoneda C) _o a)%object
      ((Yoneda C) _o (CHP a term))%object
    :=
      {|
        Trans := fun b f =>  @Prod_morph_ex C _ _ _ _ f (@t_morph C _ b)
      |}.
  
  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    eapply Prod_morph_unique; simpl_ids.
    apply Prod_morph_com_1.
    apply Prod_morph_com_2.
    rewrite <- assoc.
    rewrite Prod_morph_com_1; trivial.
    rewrite <- assoc.
    rewrite Prod_morph_com_2.
    apply t_morph_unique.
  Qed.

  Next Obligation. (* Trans_com *)
  Proof.
    symmetry.
    apply Term_Prod_rl_obligation_1.
  Qed.

  Theorem Term_Prod (a : Obj) : (((Prod_Func C) _o (a, @terminal _ term)) ≡ a)%morphism.
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