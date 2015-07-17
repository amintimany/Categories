Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Functor_Properties.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.
Require Import Adjunction.Adjunction Adjunction.Adj_Facts.
Require Import KanExt.Global KanExt.LocalFacts.NatIso
        KanExt.LocaltoGlobal KanExt.GlobaltoLocal
.

Section Facts.
  Context {C C' : Category} (p : Functor C C')
          {D : Category}.

  (** Right kan extensions are unique up to natural isomorphisms. *)
  Section Right_KanExt_Unique.
    Context (rke rke' : Right_KanExt p D).

    Definition Right_KanExt_Unique : (rke ≡≡ rke' ::> Func_Cat _ _)%morphism :=
      Adjunct_right_unique (right_kan_ext_adj rke) (right_kan_ext_adj rke').
    
    Definition Right_KanExt_Unique_points (F : Functor C D) :
      (rke _o F ≡ rke' _o F)%morphism := NatIso_Image Right_KanExt_Unique F.

  End Right_KanExt_Unique.

  (** Left kan extensions are unique up to natural isomorphisms. *)
  Section Left_KanExt_Unique.
    Context (lke lke' : Left_KanExt p D).

    Definition Left_KanExt_Unique : (lke ≡≡ lke' ::> Func_Cat _ _)%morphism :=
      Adjunct_left_unique (left_kan_ext_adj lke) (left_kan_ext_adj lke').

    Definition Left_KanExt_Unique_points (F : Functor C D) :
      (lke _o F ≡ lke' _o F)%morphism := NatIso_Image Left_KanExt_Unique F.

  End Left_KanExt_Unique.

  Section Right_KanExt_Iso.
    Context (rke : Right_KanExt p D)
            {F F' : Functor C D}
            (I : (F ≡≡ F' ::> Func_Cat _ _)%morphism).

    Definition Right_KanExt_Iso : (rke _o F ≡ rke _o F')%morphism :=
      Functors_Preserve_Isos rke I.

  End Right_KanExt_Iso.

  Section Left_KanExt_Iso.
    Context (lke : Left_KanExt p D)
            {F F' : Functor C D}
            (I : (F ≡≡ F' ::> Func_Cat _ _)%morphism).

    Definition Left_KanExt_Iso : (lke _o F ≡ lke _o F')%morphism :=
      Functors_Preserve_Isos lke I.

  End Left_KanExt_Iso.

  Section Right_KanExt_Iso_along.
    Context {p' : Functor C C'}
            (N : (p' ≡≡ p ::> Func_Cat _ _)%morphism)
            (rke : Right_KanExt p D)
    .
    
    Definition Right_KanExt_Iso_along : Right_KanExt p' D :=
      Local_to_Global_Right
        p'
        D
        (
          fun F : Functor C D =>
            Local_Right_KanExt_Iso_along
              N
              (Global_to_Local_Right p D rke F)
        ).

  End Right_KanExt_Iso_along.

  Section Left_KanExt_Iso_along.
    Context {p' : Functor C C'}
            (N : (p' ≡≡ p ::> Func_Cat _ _)%morphism)
            (lke : Left_KanExt p D)
    .
    
    Definition Left_KanExt_Iso_along : Left_KanExt p' D :=
      Local_to_Global_Left
        p'
        D
        (
          fun F : Functor C D =>
            Local_Right_KanExt_Iso_along
              (Opposite_NatIso N)
              (Global_to_Local_Left p D lke F)
        ).

  End Left_KanExt_Iso_along.  

End Facts.