Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func.
Require Import NatTrans.Main.
Require Import Ext_Cons.Prod_Cat.Main.
Require Import Adjunction.Adjunction Adjunction.Adj_Facts.
Require Import KanExt.Local KanExt.LocalFacts.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Section Right_Adjoint_Preserves_Hom_Local_Right_KanExt.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D) (hlrke : Hom_Local_Right_KanExt p F) {E : Category} {L : Functor E D} {R : Functor D E} (adj : UCU_Adjunct L R).

  Local Obligation Tactic := idtac.

  Local Definition Ext_p_F_Hom_Adjunct_Lifted := (Inverse_Isomorphism (NatIso_hor_comp (NatTrans_id_Iso (Opposite_Functor (Left_Functor_Extender p E))) (Isomorphism_Compose (Inverse_Isomorphism (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ F)) (Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C) F)))).
  
  Local Definition Conv_1 := ((NatIso_Functor_assoc (Opposite_Functor (Left_Functor_Extender p E)) (Opposite_Functor (Right_Functor_Extender L C)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D))))).

  Local Definition Conv_2 := (Inverse_Isomorphism (NatIso_hor_comp (Opposite_NatIso (Inverse_Isomorphism (Right_Left_Functor_Extension_Iso p L))) (NatTrans_id_Iso (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))))).

  Local Definition Conv_3 := (Inverse_Isomorphism (NatIso_Functor_assoc (Opposite_Functor (Right_Functor_Extender L C')) (Opposite_Functor (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D))))).

  Local Definition Conv := Isomorphism_Compose Conv_1 (Isomorphism_Compose Conv_2 Conv_3).

  Local Definition Ext_L_HLRKE_Iso := (NatIso_hor_comp (NatTrans_id_Iso (Opposite_Functor (Right_Functor_Extender L C'))) (HLRKE_Iso hlrke)).

  Local Definition Fix2_hlrke_Hom_Adjunct_Lifted := (Isomorphism_Compose (Inverse_Isomorphism (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ (hlrke))) (Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C') (hlrke))).

  Local Definition Local_Preservation_Iso_underlying := Isomorphism_Compose Ext_p_F_Hom_Adjunct_Lifted (Isomorphism_Compose Conv (Isomorphism_Compose Ext_L_HLRKE_Iso Fix2_hlrke_Hom_Adjunct_Lifted)).

  Local Definition Left_simplifier := NatIso_hor_comp (NatTrans_id_Iso (Opposite_Functor (Left_Functor_Extender p E))) (Inverse_Isomorphism (Isomorphism_Compose (Fix_Bi_2_Func_Prod_Func_NatIso (Functor_id (Func_Cat C E) ^op) (Right_Functor_Extender R C) (Hom_Func (Func_Cat C E)) F) (Fix_Bi_Func_2_NatIso (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C E))) (Functor_compose F R)))).

  Local Definition Right_simplifier := Isomorphism_Compose (Fix_Bi_2_Func_Prod_Func_NatIso (Functor_id (Func_Cat C' E) ^op) (Right_Functor_Extender R C') (Hom_Func (Func_Cat C' E)) (hlrke)) ((Fix_Bi_Func_2_NatIso (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C' E))) (Functor_compose hlrke R))).
  
  Definition Local_Preservation_Iso := Isomorphism_Compose (Isomorphism_Compose Left_simplifier Local_Preservation_Iso_underlying) Right_simplifier.

  Instance Right_Adjoint_Preserves_Hom_Local_Right_KanExt : Hom_Local_Right_KanExt p (Functor_compose F R) :=
    {
      HLRKE := (Functor_compose (HLRKE hlrke) R);
      HLRKE_Iso := Local_Preservation_Iso
    }.
  
End Right_Adjoint_Preserves_Hom_Local_Right_KanExt.

Section Right_Adjoint_Preserves_Local_Right_KanExt.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D) (lrke : Local_Right_KanExt p F) {E : Category} {L : Functor E D} {R : Functor D E} (adj : UCU_Adjunct L R).
  
  Instance Right_Adjoint_Preserves_Local_Right_KanExt : Local_Right_KanExt p (Functor_compose F R) :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt (Right_Adjoint_Preserves_Hom_Local_Right_KanExt _ _ (Local_Right_KanExt_to_Hom_Local_Right_KanExt lrke) _).
  
End Right_Adjoint_Preserves_Local_Right_KanExt.