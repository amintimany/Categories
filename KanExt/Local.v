Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.

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
    
  End Right.
  
End KanExtension.

Section Left.
  Context {C C' : Category} (p : Functor C C') {D : Category} (F : Functor C D).

  Definition Local_Left_KanExt := Local_Right_KanExt (FOP p) (FOP F).

  Existing Class Local_Left_KanExt.
  
End Left.
  
Arguments cone_apex {_ _ _ _ _} _.
Arguments cone_edge {_ _ _ _ _} _.
Arguments LoKan_Cone_Morph {_ _ _ _ _} _ _.
Arguments cone_morph {_ _ _ _ _ _ _} _.
Arguments cone_morph_com {_ _ _ _ _ _ _} _.
Arguments LRKE {_ _ _ _ _} _.
Arguments LRKE_morph_ex {_ _ _ _ _} _ _.
Arguments LRKE_morph_unique {_ _ _ _ _} _ _ _ _.
