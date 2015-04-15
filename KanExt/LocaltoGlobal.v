Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func_Prop.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
Require Import KanExt.Global KanExt.Local KanExt.LocalFacts KanExt.GlobalDuality.

Section Local_to_Global_Right.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  Context (rke : ∀ F : Functor C D,  Local_Right_KanExt p F).
  
  Section Cone_conv.
    Context {F G : Functor C D} (N : NatTrans F G) (Cn : LoKan_Cone p F).

    Instance Cone_conv : LoKan_Cone p G :=
      {
        cone_apex := Cn;
        cone_edge := NatTrans_compose Cn N
      }.

  End Cone_conv.

  Section Cone_conv_Morph_for_compose.
    Context {F G H : Functor C D} (N : NatTrans F G) (N' : NatTrans G H) (Cn : LoKan_Cone p F).

    Program Instance Cone_conv_Morph_for_compose : LoKan_Cone_Morph (Cone_conv (NatTrans_compose N N') Cn) (Cone_conv N' (Cone_conv N Cn)) :=
      {
        cone_morph := NatTrans_id Cn
      }.
    
    Next Obligation.
    Proof.
      rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_right.
      rewrite NatTrans_compose_assoc; trivial.
    Qed.      

  End Cone_conv_Morph_for_compose.

  Section Cone_Morph_conv.
    Context {F G : Functor C D} (N : NatTrans F G) {Cn Cn' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn').

    Program Instance Cone_Morph_conv : LoKan_Cone_Morph (Cone_conv N Cn) (Cone_conv N Cn') :=
      {
        cone_morph := h
      }.

    Next Obligation.
    Proof.
      unfold Cone_conv; cbn.
      rewrite NatTrans_compose_assoc.
      rewrite (cone_morph_com h).
      trivial.
    Qed.
    
  End Cone_Morph_conv.

  Section Trivial_Cone.
    Context (F : Functor C' D).

    Instance Trivial_Cone : LoKan_Cone p (Functor_compose p F) :=
      {
        cone_apex := F;
        cone_edge := NatTrans_hor_comp (NatTrans_id p) (NatTrans_id F)
      }.

  End Trivial_Cone.

  Section Trivial_Cone_Morph.
    Context {F G : Functor C' D} (N : NatTrans F G).
    
    Program Instance Trivial_Cone_Morph : LoKan_Cone_Morph (Cone_conv (NatTrans_hor_comp (NatTrans_id p) N) (Trivial_Cone F)) (Trivial_Cone G) :=
      {
        cone_morph := N
      }.

    Next Obligation.
    Proof.
      repeat rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_left.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.
      
  End Trivial_Cone_Morph.

  Section Cone_Morph_to_other_Cone.
    Context {L : Functor C' D} {F : Functor C D} (Cn : LoKan_Cone p F) (N : NatTrans L Cn).

    Program Instance Cone_Morph_to_other_Cone :
      LoKan_Cone_Morph
        (Cone_conv
           (NatTrans_compose (NatTrans_hor_comp (NatTrans_id p) N)
                             Cn) (Trivial_Cone L)) Cn :=
      {
        cone_morph := N
      }.

    Next Obligation.
      rewrite NatTrans_hor_comp_ids.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.
    
  End Cone_Morph_to_other_Cone.

  Local Obligation Tactic := idtac.
  
  Program Instance Local_to_Global_Right_Functor : Functor (Func_Cat C D) (Func_Cat C' D) :=
    {
      FO := fun F => LRKE (rke F);
      FA := fun F G N => LRKE_morph_ex (rke G) (Cone_conv N (LRKE (rke F)))
    }.
  
  Next Obligation.
  Proof.
    intros F; cbn.
    unfold Cone_conv.
    rewrite NatTrans_id_unit_left.
    change (NatTrans_id (LRKE (rke F))) with (cone_morph (LoKan_id_Cone_Morph _ _ (LRKE (rke F)))).
    apply LRKE_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    intros F G H N N'; cbn.
    match goal with
      [|- _ = ?A] =>
      match A with
      | NatTrans_compose (cone_morph ?X) (cone_morph ?Y) =>
        replace A with (NatTrans_compose (NatTrans_id _) A); [|apply NatTrans_id_unit_right];
        set (V := (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ (Cone_Morph_conv N' X) Y));
        set (Z := @Cone_conv_Morph_for_compose _ _ _ N N' (LRKE (rke F)));
        set (U := cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ Z V)); unfold V, Z in U; clear V Z
      end
    end.
    match goal with
      [|- _ = ?A] =>
      change A with U
    end.
    apply (LRKE_morph_unique (rke H) (Cone_conv (NatTrans_compose N N') (LRKE (rke F)))).
  Qed.

  Program Instance Local_to_Global_Right_adj_unit :
    NatTrans (Functor_id (Func_Cat C' D)) (Functor_compose (GExtend p D) Local_to_Global_Right_Functor) :=
    {
      Trans := fun F => LRKE_morph_ex (rke (Functor_compose p F)) (Trivial_Cone F)
    }.

  Next Obligation.
  Proof.
    intros F G N.
    cbn.
    change N with (cone_morph (Trivial_Cone_Morph N)).
    match goal with
      [|- ?X = ?Y] =>
      match X with
        NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
        change X with (cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ A B))
      end;
        match Y with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
            change Y with (cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ (Cone_Morph_conv (NatTrans_hor_comp (NatTrans_id p) N) A) B))
        end
    end.
    apply (LRKE_morph_unique (rke (Functor_compose p G)) (Cone_conv (NatTrans_hor_comp (NatTrans_id p) N) (Trivial_Cone F))).
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Local_to_Global_Right_adj_unit_obligation_1.
  Qed.

  Definition Local_to_Global_Right_adj_morph_ex (L : Functor C' D) (F : Functor C D)
    (N : NatTrans L (LRKE (rke F))) : NatTrans (Functor_compose p L) F := NatTrans_compose (NatTrans_hor_comp (NatTrans_id p) N) (cone_edge (LRKE (rke F))).

  Program Instance Local_to_Global_Right : Right_KanExt p D :=
    {
      right_kan_ext := Local_to_Global_Right_Functor;
      right_kan_ext_adj := {|
                            adj_unit := Local_to_Global_Right_adj_unit;
                            adj_morph_ex := Local_to_Global_Right_adj_morph_ex|}
    }.

  Next Obligation.
  Proof.
    intros L F h.
    unfold Local_to_Global_Right_adj_morph_ex.
    cbn in *.
    match goal with
      [|- ?X = ?Y] =>
        match Y with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
          change Y with (cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ (Cone_Morph_conv (NatTrans_compose (NatTrans_hor_comp (NatTrans_id p) h) (LRKE (rke F))) A) B))
        end
    end.
    change h with (cone_morph (Cone_Morph_to_other_Cone (LRKE (rke F)) h)).
    apply (LRKE_morph_unique (rke F) (Cone_conv
                     (NatTrans_compose (NatTrans_hor_comp (NatTrans_id p) h)
                                       (LRKE (rke F))) (Trivial_Cone L))).
  Qed.

  Next Obligation.
  Proof.
    intros L F h g g' H1 H2.
    cbn in *.
    match type of H1 with
      _ = ?X =>
      match X with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
          change X with (cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ (Cone_Morph_conv g A) B)) in H1
      end
    end.
    match type of H2 with
      _ = ?X =>
      match X with
          NatTrans_compose (cone_morph ?A) (cone_morph ?B) =>
          change X with (cone_morph (@LoKan_Cone_Morph_compose _ _ _ _ _ _ _ _ (Cone_Morph_conv g' A) B)) in H2
      end
    end.
    match type of H1 with
      _ = cone_morph ?X =>
      set (H4 := cone_morph_com X); rewrite <- H1 in H4; cbn in H4;
      match type of H2 with
        _ = cone_morph ?Y =>
        set (H3 := cone_morph_com Y); rewrite <- H2 in H3; cbn in H3
      end;
      rewrite <- H4 in H3; clear H4
    end.
    rewrite NatTrans_hor_comp_ids in H3.
    repeat rewrite NatTrans_id_unit_right in H3.
    symmetry; trivial.
  Qed.

End Local_to_Global_Right.

Section Local_to_Global_Left.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  Context (lke : ∀ F : Functor C D,  Local_Left_KanExt p F).

  Let rke := fun (F : Functor C^op D^op) => (lke (Opposite_Functor F)).

  Let Local_to_Global_Right_Dual := Local_to_Global_Right _ _ rke.

  Instance Local_to_Global_Left : Left_KanExt p D := KanExt_Right_to_Left _ _ Local_to_Global_Right_Dual.

End Local_to_Global_Left.

