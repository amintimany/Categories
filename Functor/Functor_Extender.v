Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.Main.

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

Section Right_Left_Functor_Extension_Iso.
  Context {B C D E : Category} (F : Functor B C) (G : Functor D E).

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Right_Left_Functor_Extension_Iso : (Functor_compose (Left_Functor_Extender F D) (Right_Functor_Extender G B)) ≡≡ (Functor_compose (Right_Functor_Extender G C) (Left_Functor_Extender F E)) ::> Func_Cat _ _ :=
    {
      iso_morphism := {|Trans := fun h => NatTrans_Functor_assoc_sym F h G |};
      inverse_morphism := {|Trans := fun h => NatTrans_Functor_assoc F h G |}
    }.

End Right_Left_Functor_Extension_Iso.

  