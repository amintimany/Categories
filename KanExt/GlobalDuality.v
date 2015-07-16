Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func_Prop.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.
Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
Require Import KanExt.Global.

(** In this module we establish the dualit of kan extensions.
That is, the left kan extension along p is just the right kan extension along pᵒᵖ and vice versa.

 *)
Section GlobalDuality.
  Context {C C' : Category} (p : Functor C C') (D : Category).

  (** We establish this duality though hom functor definition of adjunction. *)
  
  Local Notation GEXOP :=
    ((Op_Func_Cat_to_Func_Cat_Op C D) ∘
     ((Left_Functor_Extender p D)^op ∘ (Func_Cat_Op_to_Op_Func_Cat C' D))
    )%functor (only parsing).

  Program Definition GExtend_Duality_lr : NatTrans (Left_Functor_Extender p^op D ^op) GEXOP :=
    {|
      Trans :=  fun h => {|Trans := fun d => id |}
    |}.

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

  Program Definition GExtend_Duality_rl : NatTrans GEXOP (Left_Functor_Extender p^op D ^op) :=
    {|
      Trans :=  fun h => {|Trans := fun d => id |}
    |}.

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

  Program Definition GExtend_Duality : ((Left_Functor_Extender p^op D ^op) ≡≡ GEXOP ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := GExtend_Duality_lr;
      inverse_morphism := GExtend_Duality_rl
    |}.

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

    Program Definition KanExt_Left_to_Right : Right_KanExt  p^op D^op :=
      {|
        right_kan_ext :=
          ((Op_Func_Cat_to_Func_Cat_Op C' D) ∘
          (lke^op ∘ (Func_Cat_Op_to_Op_Func_Cat C D)))%functor
      |}.

    Next Obligation.
    Proof.
      set (V := NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor ((inverse_morphism (Func_Cat_Op_Iso C' D))^op) (inverse_morphism (Func_Cat_Op_Iso C D)))) (Isomorphism_Compose (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Left_Functor_Extender p D) (Functor_id (Func_Cat C D) ^op))) (Inverse_Isomorphism (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D)))) (Isomorphism_Compose (Hom_Adjunct_Duality (Adj_to_Hom_Adj (left_kan_ext_adj lke))) (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Functor_id ((Func_Cat C' D) ^op) ^op) lke^op)) (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D)))))).
      cbn in V.
      repeat rewrite Functor_assoc in V.
      repeat rewrite Prod_Functor_compose in V.
      do 2 rewrite Functor_id_unit_left in V.
      change ((Op_Func_Cat_to_Func_Cat_Op C D)^op ∘
              (((Left_Functor_Extender p D)) ∘
              (Func_Cat_Op_to_Op_Func_Cat C' D)^op))%functor
             with (((Op_Func_Cat_to_Func_Cat_Op C D) ∘
                  ((Left_Functor_Extender p D)^op ∘
                  (Func_Cat_Op_to_Op_Func_Cat C' D)))^op)%functor in V.
      change ((Op_Func_Cat_to_Func_Cat_Op C' D)^op ∘ (Func_Cat_Op_to_Op_Func_Cat C' D)^op)%functor
             with (((Op_Func_Cat_to_Func_Cat_Op C' D) ∘ (Func_Cat_Op_to_Op_Func_Cat C' D))^op)%functor in V.
      cbn_rewrite (right_inverse (Func_Cat_Op_Iso C D)) in V.
      cbn_rewrite (right_inverse (Func_Cat_Op_Iso C' D)) in V.
      apply (Adjunct_left_iso _ _ GExtend_Duality).
      apply Hom_Adj_to_Adj.
      exact V.
    Qed.

  End Left_to_Right.


  Section Right_to_Left.
    Context (rke : Right_KanExt p D).

    Program Definition KanExt_Right_to_Left : Left_KanExt p^op D^op :=
      {|
        left_kan_ext := ((Op_Func_Cat_to_Func_Cat_Op C' D) ∘ (rke^op ∘ (Func_Cat_Op_to_Op_Func_Cat C D)))%functor
      |}.
    
    Next Obligation.
    Proof.
      set (V := NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (inverse_morphism (Func_Cat_Op_Iso C D))^op (inverse_morphism (Func_Cat_Op_Iso C' D)))) (Isomorphism_Compose (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor rke (Functor_id (Func_Cat C' D) ^op))) (Inverse_Isomorphism (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C' D)))) (Isomorphism_Compose (Hom_Adjunct_Duality (Adj_to_Hom_Adj (right_kan_ext_adj rke))) (NatIso_hor_comp (NatTrans_id_Iso (Prod_Functor (Functor_id ((Func_Cat C D) ^op) ^op) (Left_Functor_Extender p D)^op)) (Hom_Func_Cat_Iso (Func_Cat_Op_Iso C D)))))).
      cbn in V.
      repeat rewrite Functor_assoc in V.
      repeat rewrite Prod_Functor_compose in V.
      do 2 rewrite Functor_id_unit_left in V.
      change ((Op_Func_Cat_to_Func_Cat_Op C' D)^op ∘
              (rke ∘ (Func_Cat_Op_to_Op_Func_Cat C D)^op))%functor
             with (((Op_Func_Cat_to_Func_Cat_Op C' D) ∘
              (rke^op ∘ (Func_Cat_Op_to_Op_Func_Cat C D)))^op)%functor in V.
      change  ((Op_Func_Cat_to_Func_Cat_Op C D)^op ∘
                 (Func_Cat_Op_to_Op_Func_Cat C D)^op)%functor
             with (((Op_Func_Cat_to_Func_Cat_Op C D) ∘ (Func_Cat_Op_to_Op_Func_Cat C D))^op)%functor in V.
      cbn_rewrite (right_inverse (Func_Cat_Op_Iso C D)) in V.
      cbn_rewrite (right_inverse (Func_Cat_Op_Iso C' D)) in V.
      apply (Adjunct_right_iso _ _ _ (Inverse_Isomorphism GExtend_Duality)).
      apply Hom_Adj_to_Adj.
      exact V.
    Qed.

  End Right_to_Left.

End GlobalDuality.