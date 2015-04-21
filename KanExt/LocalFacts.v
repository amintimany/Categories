Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Adjunction.Adjunction.
Require Import KanExt.Local.
Require Import Basic_Cons.Terminal.

Section Facts.
  Context {C C' : Category} (p : Functor C C')
          {D : Category} (F : Functor C D).

  Section LoKan_Cone_Morph_eq_simplify.
    Context {Cn Cn' : LoKan_Cone p F} (M M' : LoKan_Cone_Morph Cn Cn').

    Theorem LoKan_Cone_Morph_eq_simplify : M = M' :> NatTrans _ _ → M = M'.
    Proof.
      intros H.
      destruct M as [Mm Mc]; destruct M' as [Mm' Mc']; cbn in *.
      destruct H.
      destruct (proof_irrelevance _ Mc Mc').
      trivial.
    Qed.      

  End LoKan_Cone_Morph_eq_simplify.

  Section LoKan_id_Cone_Morph.
    Context (Cn : LoKan_Cone p F).

    Program Instance LoKan_id_Cone_Morph : LoKan_Cone_Morph Cn Cn :=
      {
        cone_morph := NatTrans_id _
      }.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality x.
      cbn; auto.
    Qed.        

  End LoKan_id_Cone_Morph.

  Section LoKan_Cone_Morph_compose.
    Context {Cn Cn' Cn'' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn') (h' : LoKan_Cone_Morph Cn' Cn'').

    Program Instance LoKan_Cone_Morph_compose : LoKan_Cone_Morph Cn Cn'' :=
      {
        cone_morph := NatTrans_compose h h'
      }.

    Next Obligation.
    Proof.
      rewrite (cone_morph_com h).
      rewrite (cone_morph_com h').
      rewrite NatTrans_compose_assoc.
      rewrite NatTrans_comp_hor_comp.
      rewrite NatTrans_id_unit_right.
      trivial.
    Qed.

  End LoKan_Cone_Morph_compose.

  Section LoKan_Cone_Morph_compose_assoc.
    Context {Cn Cn' Cn'' Cn''' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn') (h' : LoKan_Cone_Morph Cn' Cn'') (h'' : LoKan_Cone_Morph Cn'' Cn''').

    Theorem LoKan_Cone_Morph_compose_assoc :
      LoKan_Cone_Morph_compose h (LoKan_Cone_Morph_compose h' h'') =
      LoKan_Cone_Morph_compose (LoKan_Cone_Morph_compose h h') h''.
    Proof.
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_compose_assoc.
    Qed.      

  End LoKan_Cone_Morph_compose_assoc.

  Section LoKan_id_Cone_Morph_unit.
    Context {Cn Cn' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn').

    Theorem LoKan_id_Cone_Morph_unit_right : LoKan_Cone_Morph_compose (LoKan_id_Cone_Morph _) h = h.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_id_unit_right.
    Qed.

    Theorem LoKan_id_Cone_Morph_unit_left : LoKan_Cone_Morph_compose h (LoKan_id_Cone_Morph _) = h.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply NatTrans_id_unit_left.
    Qed.

  End LoKan_id_Cone_Morph_unit.

  (* Local kan extension cones form a category *)

  Instance LoKan_Cone_Cat : Category :=
    {
      Obj := LoKan_Cone p F;
      Hom := LoKan_Cone_Morph;
      compose := fun _ _ _ h h' => LoKan_Cone_Morph_compose h h';
      assoc := fun _ _ _ _ => LoKan_Cone_Morph_compose_assoc;
      assoc_sym := fun _ _ _ _ f g h => eq_sym (LoKan_Cone_Morph_compose_assoc f g h);
      id := LoKan_id_Cone_Morph;
      id_unit_left := @LoKan_id_Cone_Morph_unit_left;
      id_unit_right := @LoKan_id_Cone_Morph_unit_right
    }.

  Section Local_Right_KanExt_terminal.
    Context (rke : Local_Right_KanExt p F).

    Program Instance Local_Right_KanExt_terminal : Terminal LoKan_Cone_Cat :=
      {
        terminal := LRKE rke;
        t_morph := LRKE_morph_ex rke
      }.

    Next Obligation.
    Proof.    
      apply LoKan_Cone_Morph_eq_simplify.
      apply (LRKE_morph_unique rke).
    Qed.

  End Local_Right_KanExt_terminal.

  Section Local_Right_KanExt_unique.
    Context (rke rke' : Local_Right_KanExt p F).

    Theorem Local_Right_KanExt_unique : (LRKE rke) ≡≡ (LRKE rke') ::> LoKan_Cone_Cat.
    Proof (Terminal_iso (Local_Right_KanExt_terminal rke) (Local_Right_KanExt_terminal rke')).
      
  End Local_Right_KanExt_unique.

End Facts.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Section Local_Right_KanExt_to_Hom_Local_Right_KanExt.
  Context {C C' : Category} {p : Functor C C'}
          {D : Category} {F : Functor C D}
          (lrke : Local_Right_KanExt p F).

  Program Instance Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR : NatTrans (FCOMP (FOP (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D)))) (@Fix_Bi_Func_2 _ (Func_Cat C' D) _ lrke (Hom_Func (Func_Cat C' D))) :=
    {
      Trans :=  fun c h => LRKE_morph_ex lrke {|cone_apex := c; cone_edge := h|}
    }.

  Next Obligation.
  Proof.
    extensionality x.
    repeat rewrite NatTrans_id_unit_left.
    match goal with
      [|- cone_morph (LRKE_morph_ex lrke ?A) = ?X] =>
      match X with
        NCOMP ?B (cone_morph ?C) =>
        change X with (cone_morph (LoKan_Cone_Morph_compose _ _ (Build_LoKan_Cone_Morph p F A {|cone_apex := c; cone_edge := x|} h eq_refl) C))
      end
    end.
    apply LRKE_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR_obligation_1.
  Qed.

  Program Instance Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat C' D) _ lrke (Hom_Func (Func_Cat C' D))) (FCOMP (FOP (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D)))) :=
    {
      Trans :=  fun c h => NCOMP (HCOMP (NID p) h) lrke
    }.
 
  Next Obligation.
  Proof.
    extensionality x.
    repeat rewrite NatTrans_id_unit_left.
    rewrite NatTrans_compose_assoc.
    rewrite NatTrans_comp_hor_comp.
    rewrite NatTrans_id_unit_right.
    trivial.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL_obligation_1.
  Qed.
  
  Program Instance Local_Right_KanExt_to_Hom_Local_Right_KanExt : Hom_Local_Right_KanExt p F :=
    {
      HLRKE := (cone_apex (LRKE lrke));
      HLRKE_Iso :=
        {|
          iso_morphism := Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR;
          inverse_morphism := Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL
        |}
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality h; extensionality x.
    symmetry.
    apply (cone_morph_com (LRKE_morph_ex lrke {| cone_apex := h; cone_edge := x |})).
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality h; extensionality x.
    cbn in *.
    match goal with
      [|- cone_morph (LRKE_morph_ex lrke ?A) = ?X] =>
      change X with (cone_morph (Build_LoKan_Cone_Morph p F A lrke x eq_refl));
        apply (LRKE_morph_unique lrke A)
    end.
  Qed.

End Local_Right_KanExt_to_Hom_Local_Right_KanExt.


Section Hom_Local_Right_KanExt_to_Local_Right_KanExt.
  Context {C C' : Category} {p : Functor C C'}
          {D : Category} {F : Functor C D}
          (hlrke : Hom_Local_Right_KanExt p F).

  Instance Hom_Local_Right_KanExt_to_Local_Right_KanExt_Terminal_Cone : LoKan_Cone p F :=
    {
      cone_apex := hlrke;
      cone_edge := Trans (inverse_morphism (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke)
    }.

  Local Notation TCONE := Hom_Local_Right_KanExt_to_Local_Right_KanExt_Terminal_Cone (only parsing).

  Section Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone.
    Context (Cn : LoKan_Cone p F).
    
    Program Instance Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone : LoKan_Cone_Morph Cn TCONE :=
      {
        cone_morph := Trans (iso_morphism (HLRKE_Iso hlrke)) Cn Cn
      }.

    Next Obligation.
    Proof.
      set (W := f_equal (fun w : NatTrans (FCOMP (FOP (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func _))) (FCOMP (FOP (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func _))) => Trans w Cn) (left_inverse (HLRKE_Iso hlrke))).
      cbn in W.
      match goal with
        [|- ?A = ?B] =>
        match type of W with
          ?X = _ =>
          cut (X A = X B); [rewrite (equal_f W A); rewrite (equal_f W B); trivial|clear W]
        end
      end.
      apply f_equal.
      set (M := equal_f (@Trans_com _ _ _ _ (iso_morphism (HLRKE_Iso hlrke)) hlrke Cn (Trans (iso_morphism (HLRKE_Iso hlrke)) Cn Cn)) (Trans (inverse_morphism (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke))).
      cbn in M.
      repeat rewrite NatTrans_id_unit_left in M.
      rewrite M; clear M.
      apply NatTrans_eq_simplify; extensionality x; cbn.
      set (W := (f_equal (fun w : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _)) => Trans w hlrke (NatTrans_id _)) (right_inverse (HLRKE_Iso hlrke)))).
      cbn in W; rewrite W.
      simpl_ids; trivial.
    Qed.      

  End Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone.

  Section Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique.
    Context {Cn : LoKan_Cone p F} (h h' : LoKan_Cone_Morph Cn TCONE).

    Theorem Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique : h = h' :> NatTrans _ _.
    Proof.
      set (Mh := equal_f (@Trans_com _ _ _ _ (iso_morphism (HLRKE_Iso hlrke)) hlrke Cn h) (Trans (inverse_morphism (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke))).
      set (Mh' := equal_f (@Trans_com _ _ _ _ (iso_morphism (HLRKE_Iso hlrke)) hlrke Cn h') (Trans (inverse_morphism (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke))).
      cbn in Mh, Mh'.
      repeat rewrite NatTrans_id_unit_left in Mh, Mh'.
      set (H := (f_equal (fun w : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _)) => Trans w hlrke (NatTrans_id _)) (right_inverse (HLRKE_Iso hlrke)))).
      cbn in H.
      rewrite H in Mh, Mh'.
      rewrite NatTrans_id_unit_left in Mh, Mh'.
      destruct Mh; destruct Mh'.
      apply f_equal.
      apply (eq_trans (eq_sym (cone_morph_com h)) (cone_morph_com h')).
    Qed.     

  End Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique.

  Instance Hom_Local_Right_KanExt_to_Local_Right_KanExt : Local_Right_KanExt p F :=
    {
      LRKE := TCONE;
      LRKE_morph_ex := Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone;
      LRKE_morph_unique := @Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique
    }.
    
End Hom_Local_Right_KanExt_to_Local_Right_KanExt.


    