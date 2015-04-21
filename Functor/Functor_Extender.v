Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).

Section Left_Functor_Extender.
  Context {C C' : Category} (p : Functor C C') (D : Category).

    Local Hint Extern 1 => let x := fresh "x" in extensionality x; cbn.

    Local Obligation Tactic := program_simpl; auto 10.
    
    Program Instance Left_Functor_Extender :
      Functor (Func_Cat C' D) (Func_Cat C D) :=
      {
        FO := fun F => FCOMP p F;
        FA := fun F F' N => HCOMP (NID p) N
      }.

End Left_Functor_Extender.

Section Right_Functor_Extender.
  Context {C C' : Category} (p : Functor C C') (D : Category).

    Local Hint Extern 1 => let x := fresh "x" in extensionality x; cbn.

    Local Obligation Tactic := program_simpl; auto 10.
    
    Program Instance Right_Functor_Extender :
      Functor (Func_Cat D C) (Func_Cat D C') :=
      {
        FO := fun F => FCOMP F p;
        FA := fun F F' N => HCOMP N (NID p)
      }.

End Right_Functor_Extender.