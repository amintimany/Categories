Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
Require Import Adjunction.Adjunction.

Section KanExtension.
  Context {C C' : Category} (p : Functor C C').

  Local Notation FCOMP := Functor_compose (only parsing).
  Local Notation NCOMP := NatTrans_compose (only parsing).
  Local Notation HCOMP := NatTrans_hor_comp (only parsing).
  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).
  
  Section Global.
    Context (D : Category).

    Local Hint Extern 1 => let x := fresh "x" in extensionality x; cbn.

    Local Obligation Tactic := program_simpl; auto 10.
    
    Program Instance GExtend :
      Functor (Func_Cat C' D) (Func_Cat C D) :=
      {
        FO := fun F => FCOMP p F;
        FA := fun F F' N => HCOMP (NID p) N
      }.

    Class Left_KanExt : Type :=
      {
        left_kan_ext : Functor (FCAT C D) (FCAT C' D);
        left_kan_ext_adj : Adjunct left_kan_ext GExtend
      }.

    Coercion left_kan_ext : Left_KanExt >-> Functor.

    Class Right_KanExt : Type :=
      {
        right_kan_ext : Functor (FCAT C D) (FCAT C' D);
        right_kan_ext_adj : Adjunct GExtend right_kan_ext
      }.

    Coercion right_kan_ext : Right_KanExt >-> Functor.

  End Global.

End KanExtension.

Arguments left_kan_ext {_ _ _ _} _.
Arguments left_kan_ext_adj {_ _ _ _} _.

Arguments right_kan_ext {_ _ _ _} _.
Arguments right_kan_ext_adj {_ _ _ _} _.