Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
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