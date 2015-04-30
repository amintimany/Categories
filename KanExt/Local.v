Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
Require Export Functor.Functor_Extender.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Section KanExtension.
  Context {C C' : Category} (p : Functor C C').

  Section Right.
    Context {D : Category} (F : Functor C D).

    Class LoKan_Cone : Type :=
      {
        cone_apex : Functor C' D;
        cone_edge : NatTrans (FCOMP p cone_apex) F
      }.

    Coercion cone_apex : LoKan_Cone >-> Functor.
    Coercion cone_edge : LoKan_Cone >-> NatTrans.

    Section LoKan_Cone_Morph.
      Context (Cn Cn' : LoKan_Cone).

      Class LoKan_Cone_Morph : Type :=
        {
          cone_morph : NatTrans Cn Cn';
          cone_morph_com : Cn = NCOMP (HCOMP (NID p) cone_morph) Cn' :> NatTrans _ _
        }.

      Coercion cone_morph : LoKan_Cone_Morph >-> NatTrans.

    End LoKan_Cone_Morph.

    Class Local_Right_KanExt :=
      {
        LRKE : LoKan_Cone;
        LRKE_morph_ex : ∀ (Cn : LoKan_Cone), LoKan_Cone_Morph Cn LRKE;
        LRKE_morph_unique : ∀ (Cn : LoKan_Cone) (h h' : LoKan_Cone_Morph Cn LRKE), h = h' :> NatTrans _ _
      }.

    Coercion LRKE : Local_Right_KanExt >-> LoKan_Cone.

    Class is_Local_Right_KanExt (Cn_apex : Functor C' D) :=
      {
        isLRKE_Cn_edge : NatTrans (FCOMP p Cn_apex) F;
        isLRKE_morph_ex : ∀ (Cn : LoKan_Cone), LoKan_Cone_Morph Cn {|cone_apex := Cn_apex; cone_edge := isLRKE_Cn_edge|};
        isLRKE_morph_unique : ∀ (Cn : LoKan_Cone) (h h' : LoKan_Cone_Morph Cn {|cone_apex := Cn_apex; cone_edge := isLRKE_Cn_edge|}), h = h' :> NatTrans _ _
      }.

    Definition is_Local_Right_KanExt_Local_Right_KanExt {Cn_apex : Functor C' D} (ilrke : is_Local_Right_KanExt Cn_apex) : Local_Right_KanExt :=
      {|
        LRKE := {|cone_apex := Cn_apex; cone_edge := @isLRKE_Cn_edge _ ilrke|};
        LRKE_morph_ex := @isLRKE_morph_ex _ ilrke;
        LRKE_morph_unique := @isLRKE_morph_unique _ ilrke
      |}.

    Definition Local_Right_KanExt_is_Local_Right_KanExt (lrke : Local_Right_KanExt) : is_Local_Right_KanExt lrke :=
      {|
        isLRKE_Cn_edge := lrke;
        isLRKE_morph_ex := @LRKE_morph_ex lrke;
        isLRKE_morph_unique := @LRKE_morph_unique lrke
      |}.
    
  End Right.
  
End KanExtension.

Section Left.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D).

  Definition Local_Left_KanExt := Local_Right_KanExt (FOP p) (FOP F).

  Definition is_Local_Left_KanExt (Cn_apex : Functor C' D) := is_Local_Right_KanExt (FOP p) (FOP F) (FOP Cn_apex).

  Existing Class Local_Left_KanExt.
  Existing Class is_Local_Left_KanExt.
  
End Left.
  
Arguments cone_apex {_ _ _ _ _} _.
Arguments cone_edge {_ _ _ _ _} _.
Arguments LoKan_Cone_Morph {_ _ _ _ _} _ _.
Arguments cone_morph {_ _ _ _ _ _ _} _.
Arguments cone_morph_com {_ _ _ _ _ _ _} _.
Arguments LRKE {_ _ _ _ _} _.
Arguments LRKE_morph_ex {_ _ _ _ _} _ _.
Arguments LRKE_morph_unique {_ _ _ _ _} _ _ _ _.

Section Hom_Local_Right_KanExt.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D).

  Definition Hom_Local_Right_KanExt_Isomorphism (HLRKE : Functor C' D) := (FCOMP (FOP (Left_Functor_Extender p D)) (@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D)))) ≡≡ (@Fix_Bi_Func_2 _ (Func_Cat C' D) _ HLRKE (Hom_Func (Func_Cat C' D))) ::> Func_Cat _ _.
  
  Class Hom_Local_Right_KanExt := 
    {
      HLRKE : Functor C' D;
      HLRKE_Iso : Hom_Local_Right_KanExt_Isomorphism HLRKE
    }.
  
  Coercion HLRKE : Hom_Local_Right_KanExt >-> Functor.
  
End Hom_Local_Right_KanExt.

Section Hom_Local_Left_KanExt.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D).

  Definition Hom_Local_Left_KanExt := Hom_Local_Right_KanExt (FOP p) (FOP F).

  Existing Class Hom_Local_Left_KanExt.
  
End Hom_Local_Left_KanExt.

Arguments HLRKE {_ _ _ _ _} _.
Arguments HLRKE_Iso {_ _ _ _ _} _.
