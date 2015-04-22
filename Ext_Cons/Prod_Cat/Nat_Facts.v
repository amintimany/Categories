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

Section Fix_Bi_Func_1_NatTrans.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat (Func_Cat C D) B) E}
          (N : NatTrans F F') (G : Functor C D).

  Program Instance Fix_Bi_Func_1_NatTrans : NatTrans (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F') :=
    {
      Trans := fun c => Trans N (G, c)
    }.

  Next Obligation.
  Proof.
    intros c c' h.
    apply (@Trans_com _ _ _ _ N (G, c) (G, c') (NatTrans_id _, h)).
  Qed.

  Next Obligation.
  Proof.
    intros c c' h.
    apply (@Trans_com_sym _ _ _ _ N (G, c) (G, c') (NatTrans_id _, h)).
  Qed.

End Fix_Bi_Func_1_NatTrans.

Section Fix_Bi_Func_1_NatIso.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat (Func_Cat C D) B) E}
          (N : F ≡≡ F' ::> Func_Cat _ _) (G : Functor C D).

  Program Instance Fix_Bi_Func_1_NatIso : (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) ≡≡ (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F') ::> Func_Cat _ _ :=
    {
      iso_morphism := Fix_Bi_Func_1_NatTrans (iso_morphism N) G;
      inverse_morphism := Fix_Bi_Func_1_NatTrans (inverse_morphism N) G
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (inverse_morphism N) (G, c) ∘ Trans (iso_morphism N) (G, c)) with (Trans (NatTrans_compose (iso_morphism N) (inverse_morphism N)) (G, c)).
    set (W := left_inverse N); cbn in W; rewrite W; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (iso_morphism N) (G, c) ∘ Trans (inverse_morphism N) (G, c)) with (Trans (NatTrans_compose (inverse_morphism N) (iso_morphism N)) (G, c)).
    set (W := right_inverse N); cbn in W; rewrite W; trivial.
  Qed.

End Fix_Bi_Func_1_NatIso.

Section Fix_Bi_Func_2_NatTrans.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat B (Func_Cat C D)) E}
          (N : NatTrans F F') (G : Functor C D).

  Program Instance Fix_Bi_Func_2_NatTrans : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F') :=
    {
      Trans := fun c => Trans N (c, G)
    }.

  Next Obligation.
  Proof.
    intros c c' h.
    apply (@Trans_com _ _ _ _ N (c, G) (c', G) (h, NatTrans_id _)).
  Qed.

  Next Obligation.
  Proof.
    intros c c' h.
    apply (@Trans_com_sym _ _ _ _ N (c, G) (c', G) (h, NatTrans_id _)).
  Qed.

End Fix_Bi_Func_2_NatTrans.

Section Fix_Bi_Func_2_NatIso.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat B (Func_Cat C D)) E}
          (N : F ≡≡ F' ::> Func_Cat _ _) (G : Functor C D).

  Program Instance Fix_Bi_Func_2_NatIso : (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) ≡≡ (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F') ::> Func_Cat _ _ :=
    {
      iso_morphism := Fix_Bi_Func_2_NatTrans (iso_morphism N) G;
      inverse_morphism := Fix_Bi_Func_2_NatTrans (inverse_morphism N) G
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (inverse_morphism N) (c, G) ∘ Trans (iso_morphism N) (c, G)) with (Trans (NatTrans_compose (iso_morphism N) (inverse_morphism N)) (c, G)).
    set (W := left_inverse N); cbn in W; rewrite W; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (iso_morphism N) (c, G) ∘ Trans (inverse_morphism N) (c, G)) with (Trans (NatTrans_compose (inverse_morphism N) (iso_morphism N)) (c, G)).
    set (W := right_inverse N); cbn in W; rewrite W; trivial.
  Qed.

End Fix_Bi_Func_2_NatIso.

Section Fix_Bi_Func_1_Functor_id_swap_NatIso.
  Context {B B' C D E E' : Category} (F : Functor B B') (F' : Functor (Prod_Cat (Func_Cat C D) B') E)
          (G : Functor C D).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Fix_Bi_Func_1_Functor_id_swap_NatIso : (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G (Functor_compose (Prod_Functor (Functor_id _) F) F')) ≡≡ (Functor_compose F (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F')) ::> Func_Cat _ _ :=
    {
      iso_morphism :=
        {|
          Trans := fun c => id
        |};
      inverse_morphism :=
        {|
          Trans := fun c => id
        |}
    }.

End Fix_Bi_Func_1_Functor_id_swap_NatIso.

Section Fix_Bi_Func_2_Functor_id_swap_NatIso.
  Context {B B' C D E E' : Category} (F : Functor B B') (F' : Functor (Prod_Cat B' (Func_Cat C D)) E)
          (G : Functor C D).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Fix_Bi_Func_2_Functor_id_swap_NatIso : (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G (Functor_compose (Prod_Functor F (Functor_id _)) F')) ≡≡ (Functor_compose F (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F')) ::> Func_Cat _ _ :=
    {
      iso_morphism :=
        {|
          Trans := fun c => id
        |};
      inverse_morphism :=
        {|
          Trans := fun c => id
        |}
    }.

End Fix_Bi_Func_2_Functor_id_swap_NatIso.

Section Fix_Bi_1_Func_Prod_Func_NatIso.
  Context {A B C D E : Category} (F : Functor A C) (F' : Functor B D) (G : Functor (Prod_Cat C D) E) (x : A).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Fix_Bi_1_Func_Prod_Func_NatIso : (Fix_Bi_Func_1 x (Functor_compose (Prod_Functor F F') G)) ≡≡ (Fix_Bi_Func_1 (F _o x) (Functor_compose (Prod_Functor (Functor_id C) F') G)) ::> Func_Cat _ _ :=
    {
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    }.

End Fix_Bi_1_Func_Prod_Func_NatIso.

Section Fix_Bi_2_Func_Prod_Func_NatIso.
  Context {A B C D E : Category} (F : Functor A C) (F' : Functor B D) (G : Functor (Prod_Cat C D) E) (x : B).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Fix_Bi_2_Func_Prod_Func_NatIso : (Fix_Bi_Func_2 x (Functor_compose (Prod_Functor F F') G)) ≡≡ (Fix_Bi_Func_2 (F' _o x) (Functor_compose (Prod_Functor F (Functor_id D)) G)) ::> Func_Cat _ _ :=
    {
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    }.

End Fix_Bi_2_Func_Prod_Func_NatIso.

Section Func_Prod_of_ids_NatIso.
  Context {C D E : Category} (F : Functor (Prod_Cat C D) E).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Instance Func_Prod_of_ids_NatIso : (Functor_compose (Prod_Functor (Functor_id C) (Functor_id D)) F) ≡≡ F ::> Func_Cat _ _ :=
    {
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    }.

End Func_Prod_of_ids_NatIso.