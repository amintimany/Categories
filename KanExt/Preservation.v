Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func.
Require Import NatTrans.Main.
Require Import Ext_Cons.Prod_Cat.Main.
Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
Require Import KanExt.Local KanExt.LocalFacts.Main.

Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

(** Local right kan extensions are preserved by right adjoints and local left kan extensions are
preserved by left adjoints. *)
Section Right_Adjoint_Preserves_Hom_Local_Right_KanExt.
  Context
    {C C' : Category}
    (p : Functor C C')
    {D : Category}
    (F : Functor C D)
    (hlrke : Hom_Local_Right_KanExt p F)
    {E : Category}
    {L : Functor E D}
    {R : Functor D E}
    (adj : UCU_Adjunct L R)
  .
  
  (** Hom_Func_{Func_Cat C E}(- ∘ p, R ∘ F) ≡ Hom_Func_{Func_Cat C D}(L ∘ - ∘ p, F) *)
  Local Definition Ext_p_F_Hom_Adjunct_Lifted :=
    (Inverse_Isomorphism
       (NatIso_hor_comp
          (NatTrans_id_Iso (Opposite_Functor (Left_Functor_Extender p E)))
          (Isomorphism_Compose
             (Inverse_Isomorphism (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ F))
             (Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C) F)
          )
       )
    ).
  
  
  Local Definition Conv_1 :=
    (
      NatIso_Functor_assoc
       (Left_Functor_Extender p E)^op
       (Right_Functor_Extender L C)^op
       (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))
    ).

  Local Definition Conv_2 :=
    (
      Inverse_Isomorphism
        (
          NatIso_hor_comp
            (Opposite_NatIso (Inverse_Isomorphism (Right_Left_Functor_Extension_Iso p L)))
            (NatTrans_id_Iso (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D))))
       )
    ).

  Local Definition Conv_3 :=
    (
      Inverse_Isomorphism
        (
          NatIso_Functor_assoc
            ((Right_Functor_Extender L C')^op)
            ((Left_Functor_Extender p D)^op)
            (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))
        )
    ).

  Local Definition Conv := Isomorphism_Compose Conv_1 (Isomorphism_Compose Conv_2 Conv_3).

  Local Definition Ext_L_HLRKE_Iso :=
    (
      NatIso_hor_comp
        (NatTrans_id_Iso (Right_Functor_Extender L C')^op)
        (HLRKE_Iso hlrke)
    ).

  Local Definition Fix2_hlrke_Hom_Adjunct_Lifted :=
    (
      Isomorphism_Compose
        (Inverse_Isomorphism (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ (hlrke)))
        (Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C') (hlrke))
    ).

  Local Definition Local_Preservation_Iso_underlying :=
    Isomorphism_Compose
      Ext_p_F_Hom_Adjunct_Lifted
      (
        Isomorphism_Compose
          Conv
          (Isomorphism_Compose Ext_L_HLRKE_Iso Fix2_hlrke_Hom_Adjunct_Lifted)
      )
  .

  Local Definition Left_simplifier :=
    NatIso_hor_comp
      (NatTrans_id_Iso (Left_Functor_Extender p E)^op)
      (
        Inverse_Isomorphism
          (
            Isomorphism_Compose
              (
                Fix_Bi_2_Func_Prod_Func_NatIso
                  (Functor_id (Func_Cat C E) ^op)
                  (Right_Functor_Extender R C)
                  (Hom_Func (Func_Cat C E))
                  F
              )
              (
                Fix_Bi_Func_2_NatIso
                  (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C E)))
                  (R ∘ F)
              )
          )
      )
  .

  Local Definition Right_simplifier :=
    Isomorphism_Compose
      (
        Fix_Bi_2_Func_Prod_Func_NatIso
         (Functor_id (Func_Cat C' E) ^op)
         (Right_Functor_Extender R C')
         (Hom_Func (Func_Cat C' E))
         (hlrke)
      )
      (
        Fix_Bi_Func_2_NatIso
          (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C' E)))
          (R ∘ hlrke)
      ).
  
  Definition Local_Preservation_Iso :=
    Isomorphism_Compose
      (
        Isomorphism_Compose
          Left_simplifier
          Local_Preservation_Iso_underlying
      )
      Right_simplifier
  .

  Definition Right_Adjoint_Preserves_Hom_Local_Right_KanExt :
    Hom_Local_Right_KanExt p (R ∘ F) :=
    {|
      HLRKE := (R ∘ (HLRKE hlrke));
      HLRKE_Iso := Local_Preservation_Iso
    |}.
  
End Right_Adjoint_Preserves_Hom_Local_Right_KanExt.

Section Right_Adjoint_Preserves_Local_Right_KanExt.
  Context {C C' : Category}
          (p : Functor C C')
          {D : Category}
          (F : Functor C D)
          (lrke : Local_Right_KanExt p F)
          {E : Category}
          {L : Functor E D}
          {R : Functor D E}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Right_Adjoint_Preserves_Local_Right_KanExt :
    Local_Right_KanExt p (R ∘ F) :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (
        Right_Adjoint_Preserves_Hom_Local_Right_KanExt
          _
          _
          (Local_Right_KanExt_to_Hom_Local_Right_KanExt lrke)
          adj
      )
  .
  
End Right_Adjoint_Preserves_Local_Right_KanExt.

Section Left_Adjoint_Preserves_Hom_Local_Left_KanExt.
  Context {C C' : Category}
          (p : Functor C C')
          {D : Category}
          (F : Functor C D)
          (hllke : Hom_Local_Left_KanExt p F)
          {E : Category}
          {L : Functor D E}
          {R : Functor E D}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Left_Adjoint_Preserves_Hom_Local_Left_KanExt :
    Hom_Local_Left_KanExt p (L ∘ F) :=
    Right_Adjoint_Preserves_Hom_Local_Right_KanExt
      _
      _
      hllke
      (Adj_to_UCU_Adj _ _ (Adjunct_Duality (UCU_Adj_to_Adj _ _ adj)))
  .
  
End Left_Adjoint_Preserves_Hom_Local_Left_KanExt.

Section Left_Adjoint_Preserves_Local_Left_KanExt.
  Context {C C' : Category}
          (p : Functor C C')
          {D : Category}
          (F : Functor C D)
          (hllke : Local_Left_KanExt p F)
          {E : Category}
          {L : Functor D E}
          {R : Functor E D}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Left_Adjoint_Preserves_Local_Left_KanExt :
    Local_Left_KanExt p (L ∘ F) :=
    Right_Adjoint_Preserves_Local_Right_KanExt
      _
      _
      hllke
      (Adj_to_UCU_Adj _ _ (Adjunct_Duality (UCU_Adj_to_Adj _ _ adj)))
  .
  
End Left_Adjoint_Preserves_Local_Left_KanExt.
