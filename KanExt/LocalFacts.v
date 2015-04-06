Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.
Require Import KanExt.Local.

Section Facts.
  Context {C C' : Category} (p : Functor C C')
          {D : Category} (F : Functor C D).

  Local Notation FCOMP := Functor_compose (only parsing).
  Local Notation NCOMP := NatTrans_compose (only parsing).
  Local Notation HCOMP := NatTrans_hor_comp (only parsing).
  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).

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

End Facts.