Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.

Local Obligation Tactic := idtac.

Section Prod_Functor_NatTrans.
  Context {C D : Category} {F G : Functor C D} (N : NatTrans F G)
          {C' D' : Category} {F' G' : Functor C' D'} (N' : NatTrans F' G').

  Program Instance Prod_Functor_NatTrans : NatTrans (Prod_Functor F F') (Prod_Functor G G') :=
    {
      Trans := fun c => (Trans N (fst c), Trans N' (snd c))
    }.

  Next Obligation.
    intros c c' h.
    cbn.
    do 2 rewrite Trans_com; trivial.
  Qed.

  Next Obligation.
    symmetry.
    apply Prod_Functor_NatTrans_obligation_1.
  Qed.

End Prod_Functor_NatTrans.

Section Prod_Functor_NatTrans_id.
  Context {C D : Category} (F : Functor C D)
          {C' D' : Category} {F' : Functor C' D'}.

  Theorem Prod_Functor_NatTrans_id : Prod_Functor_NatTrans (NatTrans_id F) (NatTrans_id F') = NatTrans_id (Prod_Functor F F').
  Proof.
    apply NatTrans_eq_simplify; trivial.
  Qed.    

End Prod_Functor_NatTrans_id.

Section Prod_Functor_NatTrans_compose.
  Context {C D : Category} {F G H : Functor C D} (N1 : NatTrans F G) (N2 : NatTrans G H)
          {C' D' : Category} {F' G' H' : Functor C' D'} (N1' : NatTrans F' G') (N2' : NatTrans G' H').

  Theorem Prod_Functor_NatTrans_compose : NatTrans_compose (Prod_Functor_NatTrans N1 N1') (Prod_Functor_NatTrans N2 N2') = Prod_Functor_NatTrans (NatTrans_compose N1 N2) (NatTrans_compose N1' N2').
  Proof.
    apply NatTrans_eq_simplify; trivial.
  Qed.

End Prod_Functor_NatTrans_compose.

Section Prod_Functor_NatIso.
  Context {C D : Category} {F G : Functor C D} (N : F ≡≡ G ::> Func_Cat _ _)
          {C' D' : Category} {F' G' : Functor C' D'} (N' : F' ≡≡ G' ::> Func_Cat _ _).

  Program Instance Prod_Functor_NatIso : (Prod_Functor F F') ≡≡ (Prod_Functor G G') ::> Func_Cat _ _ :=
    {
      iso_morphism := Prod_Functor_NatTrans (iso_morphism N) (iso_morphism N');
      inverse_morphism := Prod_Functor_NatTrans (inverse_morphism N) (inverse_morphism N')
    }.

  Next Obligation.
    cbn.
    rewrite Prod_Functor_NatTrans_compose.
    change (NatTrans_compose (iso_morphism N) N ⁻¹) with (N⁻¹ ∘ N).
    change (NatTrans_compose (iso_morphism N') N' ⁻¹) with (N'⁻¹ ∘ N').
    do 2 rewrite (left_inverse).
    apply Prod_Functor_NatTrans_id.
  Qed.

  Next Obligation.
    cbn.
    rewrite Prod_Functor_NatTrans_compose.
    change (NatTrans_compose N ⁻¹ (iso_morphism N)) with (N ∘ N⁻¹).
    change (NatTrans_compose N' ⁻¹ (iso_morphism N')) with (N' ∘ N'⁻¹).
    do 2 rewrite (right_inverse).
    apply Prod_Functor_NatTrans_id.
  Qed.

End Prod_Functor_NatIso.