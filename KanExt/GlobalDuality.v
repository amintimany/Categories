Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func_Prop.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
Require Import KanExt.Global.


Section GlobalDuality.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  Local Notation GEXOP := (Functor_compose
                 (Functor_compose (Func_Cat_Op_to_Op_Func_Cat C' D)
                    (Opposite_Functor (GExtend p D)))
                 (Op_Func_Cat_to_Func_Cat_Op C D)) (only parsing).

  Program Instance GExtend_Duality_lr : NatTrans (GExtend (Opposite_Functor p) D ^op) GEXOP :=
    {
      Trans :=  fun h => {|Trans := fun d => id |}
    }.

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros c c' h.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    simpl_ids.
    rewrite (F_id c).
    rewrite (F_id c').
    etransitivity; [apply (@id_unit_right D)| symmetry; apply (@id_unit_left D)].
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply GExtend_Duality_lr_obligation_3.
  Qed.

  Program Instance GExtend_Duality_rl : NatTrans GEXOP (GExtend (Opposite_Functor p) D ^op) :=
    {
      Trans :=  fun h => {|Trans := fun d => id |}
    }.

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros F c c' h; cbn.
    simpl_ids; trivial.
  Qed.

  Next Obligation.
  Proof.
    intros F c c' h; cbn.
    simpl_ids; trivial.
  Qed.
    
  Next Obligation.
  Proof.
    intros c c' h.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    simpl_ids.
    rewrite (F_id c).
    rewrite (F_id c').
    etransitivity; [apply (@id_unit_left D)| symmetry; apply (@id_unit_right D)].
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply GExtend_Duality_rl_obligation_3.
  Qed.

  Program Instance GExtend_Duality : (GExtend (Opposite_Functor p) D ^op) ≡≡ GEXOP ::> Func_Cat _ _ :=
    {
      iso_morphism := GExtend_Duality_lr;
      inverse_morphism := GExtend_Duality_rl
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x.
    apply NatTrans_eq_simplify; extensionality y.
    cbn.
    repeat rewrite F_id; repeat rewrite (F_id x); trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x.
    apply NatTrans_eq_simplify; extensionality y.
    cbn.
    repeat rewrite F_id; repeat rewrite (F_id x); trivial.
  Qed.

  Section Left_to_Right.
    Context (lke : Left_KanExt p D).

    Program Instance KanExt_Left_to_Right : Right_KanExt (Opposite_Functor p) D^op :=
      {
        right_kan_ext := Functor_compose
                           (Functor_compose (Func_Cat_Op_to_Op_Func_Cat C D)
                                            (Opposite_Functor lke)) (Op_Func_Cat_to_Func_Cat_Op C' D)
      }.

    Next Obligation.
    Proof.
      set (V := NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Opposite_Functor (inverse_morphism (Func_Cat_Op_Iso C' D))) (inverse_morphism (Func_Cat_Op_Iso C D)))) (NatIso_compose (NatIso_hor_comp (NatTrans_id_Iso (Prod_Cat.Prod_Functor (Opposite_Functor (Opposite_Functor (GExtend p D))) (Functor_id (Func_Cat C D) ^op))) (Inverse_Isomorphism (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D)))) (NatIso_compose (Hom_Adjunct_Duality (Adj_to_Hom_Adj (left_kan_ext_adj lke))) (NatIso_hor_comp (NatTrans_id_Iso (Prod_Cat.Prod_Functor (Functor_id ((Func_Cat C' D) ^op) ^op) (Opposite_Functor lke))) (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D)))))).
      cbn in V.
      repeat rewrite Functor_assoc in V.
      repeat rewrite Prod_Functor_compose in V.
      do 2 rewrite Functor_id_unit_left in V.
      change (Functor_compose
              (Functor_compose
                 (Opposite_Functor (Func_Cat_Op_to_Op_Func_Cat C' D))
                 (Opposite_Functor (Opposite_Functor (GExtend p D))))
              (Opposite_Functor (Op_Func_Cat_to_Func_Cat_Op C D)))
             with (Opposite_Functor (Functor_compose
              (Functor_compose
                 (Func_Cat_Op_to_Op_Func_Cat C' D)
                 (Opposite_Functor (GExtend p D)))
              (Op_Func_Cat_to_Func_Cat_Op C D))) in V.
      change (Functor_compose
                 (Opposite_Functor (Func_Cat_Op_to_Op_Func_Cat C' D))
                 (Opposite_Functor (Op_Func_Cat_to_Func_Cat_Op C' D)))
             with (Opposite_Functor (Functor_compose
                     (Func_Cat_Op_to_Op_Func_Cat C' D)
                     (Op_Func_Cat_to_Func_Cat_Op C' D))) in V.
      set (J := right_inverse (Func_Cat_Op_Iso C D)); cbn in J; rewrite J in V; clear J.
      set (K := right_inverse (Func_Cat_Op_Iso C' D)); cbn in K; rewrite K in V; clear K.
      apply (Adjunct_left_iso _ _ GExtend_Duality).
      apply Hom_Adj_to_Adj.
      exact V.
    Qed.

  End Left_to_Right.


  Section Right_to_Left.
    Context (rke : Right_KanExt p D).

    Program Instance KanExt_Right_to_Left : Left_KanExt (Opposite_Functor p) D^op :=
      {
        left_kan_ext := Functor_compose
                           (Functor_compose (Func_Cat_Op_to_Op_Func_Cat C D)
                                            (Opposite_Functor rke)) (Op_Func_Cat_to_Func_Cat_Op C' D)
      }.
    
    Next Obligation.
    Proof.
      set (V := NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Opposite_Functor (inverse_morphism (Func_Cat_Op_Iso C D))) (inverse_morphism (Func_Cat_Op_Iso C' D)))) (NatIso_compose (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Opposite_Functor (Opposite_Functor rke)) (Functor_id (Func_Cat C' D) ^op))) (Inverse_Isomorphism (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D)))) (NatIso_compose (Hom_Adjunct_Duality (Adj_to_Hom_Adj (right_kan_ext_adj rke))) (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Functor_id ((Func_Cat C D) ^op) ^op) (Opposite_Functor (GExtend p D)))) (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D)))))).
      cbn in V.
      repeat rewrite Functor_assoc in V.
      repeat rewrite Prod_Functor_compose in V.
      do 2 rewrite Functor_id_unit_left in V.
      change (Functor_compose
              (Functor_compose
                 (Opposite_Functor (Func_Cat_Op_to_Op_Func_Cat C D))
                 (Opposite_Functor (Opposite_Functor rke)))
              (Opposite_Functor (Op_Func_Cat_to_Func_Cat_Op C' D)))
             with (Opposite_Functor (Functor_compose
              (Functor_compose
                 (Func_Cat_Op_to_Op_Func_Cat C D)
                 (Opposite_Functor rke))
              (Op_Func_Cat_to_Func_Cat_Op C' D))) in V.
      change  (Functor_compose
                 (Opposite_Functor (Func_Cat_Op_to_Op_Func_Cat C D))
                 (Opposite_Functor (Op_Func_Cat_to_Func_Cat_Op C D)))
             with (Opposite_Functor (Functor_compose
                 (Func_Cat_Op_to_Op_Func_Cat C D)
                 (Op_Func_Cat_to_Func_Cat_Op C D))) in V.
      set (J := right_inverse (Func_Cat_Op_Iso C D)); cbn in J; rewrite J in V; clear J.
      set (K := right_inverse (Func_Cat_Op_Iso C' D)); cbn in K; rewrite K in V; clear K.
      apply (Adjunct_right_iso _ _ _ (Inverse_Isomorphism GExtend_Duality)).
      apply Hom_Adj_to_Adj.
      exact V.
    Qed.

  End Right_to_Left.

End GlobalDuality.