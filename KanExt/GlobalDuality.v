Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.
Require Import KanExt.Global.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NOP := Opposite_NatTrans (only parsing).

(**
Conversion from global left kan extension global right kan extension of opposite functors and vice versa. This is in fact the more general version of the fact that limits are colimits of the opposite functor and vice versa.

*)

Section LeftToRight.
  Context {C C' : Category} {p : Functor C C'}
          {D : Category} {F : Functor C D}.
  
  Section LoKan_CoCone_to_Cone.
    Context (CCn : LoKan_CoCone p F).

    Instance Cone_of_CoCone : LoKan_Cone (FOP p) (FOP F) :=
      {
        cone_apex := FOP (cocone_apex CCn);
        cone_edge := NOP (cocone_edge CCn)
      }.

  End LoKan_CoCone_to_Cone.

  Section LoKan_Cone_Op_to_CoCone.
    Context (CCn : LoKan_Cone (FOP p) (FOP F)).

    Instance CoCone_of_Cone_Op : LoKan_CoCone p F :=
      {
        cocone_apex := FOP (cone_apex CCn);
        cocone_edge := NOP (cone_edge CCn)
      }.

  End LoKan_Cone_Op_to_CoCone.
  
  Section LoKan_CoCone_Morph_to_Cone_Morph.
    Context {CCn CCn' : LoKan_CoCone p F} (h : LoKan_CoCone_Morph CCn CCn').

    Program Instance Cone_Morph_of_CoCone_Morph : LoKan_Cone_Morph (Cone_of_CoCone CCn') (Cone_of_CoCone CCn) :=
      {
        cone_morph :=  NOP (cocone_morph h)
      }.

    Next Obligation.
    Proof.
      rewrite <- NatTrans_id_Op.
      rewrite <- NatTrans_hor_comp_Op.
      change (FCOMP (FOP p) (FOP CCn)) with (FOP (FCOMP p CCn)).
      change (FCOMP (FOP p) (FOP CCn')) with (FOP (FCOMP p CCn')).
      rewrite <- NatTrans_compose_Op.
      apply f_equal.
      apply cocone_morph_com.
    Qed.

  End LoKan_CoCone_Morph_to_Cone_Morph.

  Section LoKan_Cone_Morph_Op_to_CoCone_Morph.
    Context {CCn CCn' : LoKan_Cone (FOP p) (FOP F)} (h : LoKan_Cone_Morph CCn CCn').

    Program Instance CoCone_Morph_of_Cone_Morph_Op : LoKan_CoCone_Morph (CoCone_of_Cone_Op CCn') (CoCone_of_Cone_Op CCn) :=
      {
        cocone_morph :=  NOP (cone_morph h)
      }.

    Next Obligation.
    Proof.
      etransitivity; [exact (@f_equal _ _ NOP _ _ (cone_morph_com h)) |].
      rewrite NatTrans_compose_Op.
      rewrite NatTrans_hor_comp_Op.
      rewrite NatTrans_id_Op.
      trivial.
    Qed.

  End LoKan_Cone_Morph_Op_to_CoCone_Morph.
  
  Section Local_Left_KanExt_to_Local_Right_KanExt.
    Context (llke : Local_Left_KanExt p F).

    Program Instance Local_Right_KanExt_of_Local_Left_KanExt : Local_Right_KanExt (FOP p) (FOP F) :=
      {
        LRKE := Cone_of_CoCone (LLKE llke);
        LRKE_morph_ex := fun Cn => Cone_Morph_of_CoCone_Morph (LLKE_morph_ex llke (CoCone_of_Cone_Op Cn))
      }.
    
    Next Obligation.
    Proof.
      change Cn with (Cone_of_CoCone (CoCone_of_Cone_Op Cn)) in *.
      change (cone_morph h) with (NOP (CoCone_Morph_of_Cone_Morph_Op h)). 
      change (cone_morph h') with (NOP (CoCone_Morph_of_Cone_Morph_Op h')). 
      apply f_equal.
      eapply LLKE_morph_unique.
    Qed.
  End Local_Left_KanExt_to_Local_Right_KanExt.

End LeftToRight.

Section RightToLeft.
  Context {C C' : Category} {p : Functor C C'}
          {D : Category} {F : Functor C D}.

  Section Local_Right_KanExt_to_Local_Left_KanExt.
    Context (lrke : Local_Right_KanExt p F).

    Program Instance Local_Left_KanExt_of_Local_Right_KanExt : Local_Left_KanExt (FOP p) (FOP F) :=
      {
        LLKE := @CoCone_of_Cone_Op _ _ (FOP p) _ (FOP F) (LRKE lrke);
        LLKE_morph_ex := fun Cn => @CoCone_Morph_of_Cone_Morph_Op _ _ (FOP p) _ (FOP F) _ _ (LRKE_morph_ex lrke (Cone_of_CoCone Cn))
      }.
    
    Next Obligation.
    Proof.
      change Cn with (CoCone_of_Cone_Op (Cone_of_CoCone Cn)) in *.
      change (cocone_morph h) with (NOP (Cone_Morph_of_CoCone_Morph h)). 
      change (cocone_morph h') with (NOP (Cone_Morph_of_CoCone_Morph h')). 
      apply f_equal.
      eapply LRKE_morph_unique.
    Qed.
  End Local_Right_KanExt_to_Local_Left_KanExt.

End RightToLeft.