Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func_Prop.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
Require Import KanExt.Global KanExt.Local KanExt.LocalFacts KanExt.GlobalDuality.

Section Global_to_Local_Right.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  Context (rke : Right_KanExt p D).

  Context (F : Functor C D).

  Instance Cone_for_LoKan : LoKan_Cone p F :=
    {
      cone_apex := rke _o F;
      cone_edge := @adj_morph_ex _ _ _ _ (right_kan_ext_adj rke) (rke _o F) F (NatTrans_id _)
    }.

  Section Cone_Morph_to_Cone_for_LoKan.
    Context (Cn : LoKan_Cone p F).

    Lemma Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id (morph : NatTrans Cn ((rke _o) F)) :
      morph =
      NatTrans_compose
        (Trans (adj_unit (right_kan_ext_adj rke)) Cn)
        ((rke _a) (Functor_compose p Cn) F
                  (NatTrans_compose
                     (NatTrans_hor_comp (NatTrans_id p) morph)
                     (adj_morph_ex (right_kan_ext_adj rke) (NatTrans_id ((rke _o) F))))).
    Proof.
      rewrite (@F_compose _ _ rke); cbn.
      rewrite NatTrans_compose_assoc.
      set (V := @Trans_com _ _ _ _ (@adj_unit _ _ _ _ (right_kan_ext_adj rke)) _ _ morph);
        cbn in V; rewrite <- V; clear V.
      rewrite <- NatTrans_compose_assoc.
      set (W := (@adj_morph_com _ _ _ _ (right_kan_ext_adj rke)) _ _ (NatTrans_id ((rke _o) F)));
        cbn in W; rewrite <- W.
      rewrite NatTrans_id_unit_left.
      trivial.
    Qed.

      
    Program Instance Cone_Morph_to_Cone_for_LoKan : LoKan_Cone_Morph Cn Cone_for_LoKan :=
      {
        cone_morph := NatTrans_compose (Trans (adj_unit (right_kan_ext_adj rke)) Cn) (rke _a _ _ (cone_edge Cn))
      }.

    Next Obligation.
    Proof.
      match goal with
        [|- _ = NatTrans_compose (NatTrans_hor_comp _ ?X) ?Y] =>
        apply (@adj_morph_unique _ _ _ _ (right_kan_ext_adj rke) _ _ X); trivial
      end.
      apply Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id.
    Qed.

  End Cone_Morph_to_Cone_for_LoKan.

  Section Cone_Morph_to_Cone_for_LoKan_Unique.
    Context {Cn : LoKan_Cone p F} (M M' : LoKan_Cone_Morph Cn Cone_for_LoKan).

    Theorem Cone_Morph_to_Cone_for_LoKan_Unique : (M = M' :> NatTrans _ _).
    Proof.
      rewrite (Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id Cn M).
      rewrite (Cone_Morph_to_Cone_for_LoKan_adj_unit_rke_id Cn M').
      do 2 apply f_equal.
      set (H := cone_morph_com M'); rewrite (cone_morph_com M) in H; exact H.
    Qed.
      
  End Cone_Morph_to_Cone_for_LoKan_Unique.

  Instance Global_to_Local_Right : Local_Right_KanExt p F :=
    {
      LRKE := Cone_for_LoKan;
      LRKE_morph_ex := Cone_Morph_to_Cone_for_LoKan;
      LRKE_morph_unique := @Cone_Morph_to_Cone_for_LoKan_Unique
    }.

End Global_to_Local_Right.
  
Section Global_to_Local_Left.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  Context (lke : Left_KanExt p D).

  Context (F : Functor C D).

  Let rke := KanExt_Left_to_Right _ _ lke.

  Let Global_to_Local_Right_Dual := Global_to_Local_Right _ _ rke (Opposite_Functor F).

  Instance Global_to_Local_Left : Local_Left_KanExt p F := Global_to_Local_Right_Dual.

End Global_to_Local_Left.
