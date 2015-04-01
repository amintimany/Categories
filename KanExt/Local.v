Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.

Section KanExtension.
  Context {C C' : Category} (p : Functor C C').

  Local Notation FCOMP := Functor_compose (only parsing).
  Local Notation NCOMP := NatTrans_compose (only parsing).
  Local Notation HCOMP := NatTrans_hor_comp (only parsing).
  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).

  Section Local.
    Context {D : Category} (F : Functor C D).

    Class LoKan_CoCone : Type :=
      {
        cocone_apex : Functor C' D;
        cocone_edge : NatTrans F (FCOMP p cocone_apex)
      }.

    Coercion cocone_apex : LoKan_CoCone >-> Functor.
    Coercion cocone_edge : LoKan_CoCone >-> NatTrans.

    Section LoKan_CoCone_Morph.
      Context (Cn Cn' : LoKan_CoCone).

      Class LoKan_CoCone_Morph : Type :=
        {
          cocone_morph : NatTrans Cn Cn';
          cocone_morph_com : Cn' = NCOMP Cn (HCOMP (NID p) cocone_morph) :> NatTrans _ _
        }.

      Coercion cocone_morph : LoKan_CoCone_Morph >-> NatTrans.

    End LoKan_CoCone_Morph.

    Class Local_Left_KanExt :=
      {
        LLKE : LoKan_CoCone;
        LLKE_morph_ex : ∀ (Cn : LoKan_CoCone), LoKan_CoCone_Morph LLKE Cn;
        LLKE_morph_unique : ∀ (Cn : LoKan_CoCone) (h h' : LoKan_CoCone_Morph LLKE Cn), h = h' :> NatTrans _ _
      }.

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
    
  End Local.

End KanExtension.

Arguments cocone_apex {_ _ _ _ _} _.
Arguments cocone_edge {_ _ _ _ _} _.
Arguments LoKan_CoCone_Morph {_ _ _ _ _} _ _.
Arguments cocone_morph {_ _ _ _ _ _ _} _.
Arguments cocone_morph_com {_ _ _ _ _ _ _} _.
Arguments LLKE {_ _ _ _ _} _.
Arguments LLKE_morph_ex {_ _ _ _ _} _ _.
Arguments LLKE_morph_unique {_ _ _ _ _} _ _ _ _.

Arguments cone_apex {_ _ _ _ _} _.
Arguments cone_edge {_ _ _ _ _} _.
Arguments LoKan_Cone_Morph {_ _ _ _ _} _ _.
Arguments cone_morph {_ _ _ _ _ _ _} _.
Arguments cone_morph_com {_ _ _ _ _ _ _} _.
Arguments LRKE {_ _ _ _ _} _.
Arguments LRKE_morph_ex {_ _ _ _ _} _ _.
Arguments LRKE_morph_unique {_ _ _ _ _} _ _ _ _.