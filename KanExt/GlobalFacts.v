Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction Adjunction.Adj_Facts.
Require Import KanExt.Global.

Section Facts.
  Context {C C' : Category} (p : Functor C C')
          {D : Category}.

  Section Right_KanExt_Unique.
    Context (rke rke' : Right_KanExt p D).

    Theorem Right_KanExt_Unique : rke ≡≡ rke' ::> Func_Cat _ _.
    Proof.
      apply (Adjunct_right_unique (right_kan_ext_adj rke) (right_kan_ext_adj rke') ).
    Qed.

  End Right_KanExt_Unique.

  Section Left_KanExt_Unique.
    Context (lke lke' : Left_KanExt p D).

    Theorem Left_KanExt_Unique : lke ≡≡ lke' ::> Func_Cat _ _.
    Proof.
      apply (Adjunct_left_unique (left_kan_ext_adj lke) (left_kan_ext_adj lke') ).
    Qed.

  End Left_KanExt_Unique.
  
End Facts.