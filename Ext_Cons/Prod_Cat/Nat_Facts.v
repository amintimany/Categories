Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.

(** Facts about products of acategories involving natural transformations. *)
  
Local Obligation Tactic := idtac.

Section Prod_Functor_NatTrans.
  Context {C D : Category} {F G : Functor C D} (N : NatTrans F G)
          {C' D' : Category} {F' G' : Functor C' D'} (N' : NatTrans F' G').

  Program Definition Prod_Functor_NatTrans : NatTrans (Prod_Functor F F') (Prod_Functor G G') :=
    {|
      Trans := fun c => (Trans N (fst c), Trans N' (snd c))
    |}.

  Next Obligation.
    basic_simpl.
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

  Theorem Prod_Functor_NatTrans_compose : ((Prod_Functor_NatTrans N2 N2') ∘ (Prod_Functor_NatTrans N1 N1') = Prod_Functor_NatTrans (N2 ∘ N1) (N2' ∘ N1'))%nattrans.
  Proof.
    apply NatTrans_eq_simplify; trivial.
  Qed.

End Prod_Functor_NatTrans_compose.

Section Prod_Functor_NatIso.
  Context {C D : Category} {F G : Functor C D} (N : (F ≡≡ G ::> Func_Cat _ _)%morphism)
          {C' D' : Category} {F' G' : Functor C' D'} (N' : (F' ≡≡ G' ::> Func_Cat _ _)%morphism).

  Program Definition Prod_Functor_NatIso : ((Prod_Functor F F') ≡≡ (Prod_Functor G G') ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := Prod_Functor_NatTrans (iso_morphism N) (iso_morphism N');
      inverse_morphism := Prod_Functor_NatTrans (inverse_morphism N) (inverse_morphism N')
    |}.

  Next Obligation.
    cbn.
    rewrite Prod_Functor_NatTrans_compose.
    change ((N ⁻¹)%morphism ∘ (iso_morphism N))%nattrans with (N⁻¹ ∘ N)%morphism.
    change ((N' ⁻¹)%morphism ∘ (iso_morphism N'))%nattrans with (N'⁻¹ ∘ N')%morphism.
    do 2 rewrite (left_inverse).
    apply Prod_Functor_NatTrans_id.
  Qed.

  Next Obligation.
    cbn.
    rewrite Prod_Functor_NatTrans_compose.
    change ((iso_morphism N) ∘ (N ⁻¹)%morphism)%nattrans with (N ∘ N⁻¹)%morphism.
    change ((iso_morphism N') ∘ (N' ⁻¹)%morphism)%nattrans with (N' ∘ N'⁻¹)%morphism.
    do 2 rewrite (right_inverse).
    apply Prod_Functor_NatTrans_id.
  Qed.

End Prod_Functor_NatIso.

Section Fix_Bi_Func_1_NatTrans.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat (Func_Cat C D) B) E}
          (N : NatTrans F F') (G : Functor C D).

  Program Definition Fix_Bi_Func_1_NatTrans : NatTrans (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F') :=
    {|
      Trans := fun c => Trans N (G, c)
    |}.

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
          (N : (F ≡≡ F' ::> Func_Cat _ _)%morphism) (G : Functor C D).

  Program Definition Fix_Bi_Func_1_NatIso : ((@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) ≡≡ (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F') ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := Fix_Bi_Func_1_NatTrans (iso_morphism N) G;
      inverse_morphism := Fix_Bi_Func_1_NatTrans (inverse_morphism N) G
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (inverse_morphism N) (G, c) ∘ Trans (iso_morphism N) (G, c))%morphism with (Trans ((inverse_morphism N) ∘ (iso_morphism N)) (G, c)).
    cbn_rewrite (left_inverse N); trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    change (Trans (iso_morphism N) (G, c) ∘ Trans (inverse_morphism N) (G, c))%morphism with (Trans ((iso_morphism N) ∘ (inverse_morphism N)) (G, c)).
    cbn_rewrite (right_inverse N); trivial.
  Qed.

End Fix_Bi_Func_1_NatIso.

Section Fix_Bi_Func_2_NatTrans.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat B (Func_Cat C D)) E}
          (N : NatTrans F F') (G : Functor C D).

  Program Definition Fix_Bi_Func_2_NatTrans : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F') :=
    {|
      Trans := fun c => Trans N (c, G)
    |}.

  Next Obligation.
  Proof.
    intros; apply (@Trans_com _ _ _ _ N).
  Qed.

  Next Obligation.
  Proof.
    intros; apply (@Trans_com_sym _ _ _ _ N).
  Qed.

End Fix_Bi_Func_2_NatTrans.

Section Fix_Bi_Func_2_NatIso.
  Context {B C D E : Category} {F F' : Functor (Prod_Cat B (Func_Cat C D)) E}
          (N : (F ≡≡ F' ::> Func_Cat _ _)%morphism) (G : Functor C D).

  Program Definition Fix_Bi_Func_2_NatIso : ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) ≡≡ (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F') ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := Fix_Bi_Func_2_NatTrans (iso_morphism N) G;
      inverse_morphism := Fix_Bi_Func_2_NatTrans (inverse_morphism N) G
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (inverse_morphism N) (c, G) ∘ Trans (iso_morphism N) (c, G))%morphism with (Trans ((inverse_morphism N) ∘ (iso_morphism N)) (c, G)).
    cbn_rewrite (left_inverse N); trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c.
    cbn.
    change (Trans (iso_morphism N) (c, G) ∘ Trans (inverse_morphism N) (c, G))%morphism with (Trans ((iso_morphism N) ∘ (inverse_morphism N)) (c, G)).
    cbn_rewrite (right_inverse N); trivial.
  Qed.

End Fix_Bi_Func_2_NatIso.

Section Fix_Bi_Func_1_Functor_id_swap_NatIso.
  Context {B B' C D E E' : Category} (F : Functor B B') (F' : Functor (Prod_Cat (Func_Cat C D) B') E)
          (G : Functor C D).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Fix_Bi_Func_1_Functor_id_swap_NatIso : ((@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G ( F' ∘ (Prod_Functor (Functor_id _) F))) ≡≡ ((@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F') ∘ F) ::> Func_Cat _ _)%functor%morphism :=
    {|
      iso_morphism :=
        {|
          Trans := fun c => id
        |};
      inverse_morphism :=
        {|
          Trans := fun c => id
        |}
    |}.

End Fix_Bi_Func_1_Functor_id_swap_NatIso.

Section Fix_Bi_Func_2_Functor_id_swap_NatIso.
  Context {B B' C D E E' : Category} (F : Functor B B') (F' : Functor (Prod_Cat B' (Func_Cat C D)) E)
          (G : Functor C D).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Fix_Bi_Func_2_Functor_id_swap_NatIso : ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G (F' ∘ (Prod_Functor F (Functor_id _)))) ≡≡ ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F') ∘ F) ::> Func_Cat _ _)%functor%morphism :=
    {|
      iso_morphism :=
        {|
          Trans := fun c => id
        |};
      inverse_morphism :=
        {|
          Trans := fun c => id
        |}
    |}.

End Fix_Bi_Func_2_Functor_id_swap_NatIso.

Section Fix_Bi_1_Func_Prod_Func_NatIso.
  Context {A B C D E : Category} (F : Functor A C) (F' : Functor B D) (G : Functor (Prod_Cat C D) E) (x : A).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Fix_Bi_1_Func_Prod_Func_NatIso : ((Fix_Bi_Func_1 x (G ∘ (Prod_Functor F F'))) ≡≡ (Fix_Bi_Func_1 (F _o x) (G ∘ (Prod_Functor (Functor_id C) F'))) ::> Func_Cat _ _)%functor%morphism :=
    {|
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    |}.

End Fix_Bi_1_Func_Prod_Func_NatIso.

Section Fix_Bi_2_Func_Prod_Func_NatIso.
  Context {A B C D E : Category} (F : Functor A C) (F' : Functor B D) (G : Functor (Prod_Cat C D) E) (x : B).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Fix_Bi_2_Func_Prod_Func_NatIso : ((Fix_Bi_Func_2 x (G ∘ (Prod_Functor F F'))) ≡≡ (Fix_Bi_Func_2 (F' _o x) (G ∘  (Prod_Functor F (Functor_id D)))) ::> Func_Cat _ _)%functor%morphism :=
    {|
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    |}.

End Fix_Bi_2_Func_Prod_Func_NatIso.

Section Func_Prod_of_ids_NatIso.
  Context {C D E : Category} (F : Functor (Prod_Cat C D) E).

  Local Obligation Tactic := cbn; auto.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Func_Prod_of_ids_NatIso : ((F ∘ (Prod_Functor (Functor_id C) (Functor_id D))) ≡≡ F ::> Func_Cat _ _)%functor%morphism :=
    {|
      iso_morphism := {|Trans := fun c => id|};
      inverse_morphism := {|Trans := fun c => id|}
    |}.

End Func_Prod_of_ids_NatIso.

Section Fix_Bi_Func_1_object_NatTrans.
  Context {B C D E : Category} (F : Functor (Prod_Cat (Func_Cat C D) B) E)
          {G G' : Functor C D} (N : NatTrans G G').

  Program Definition Fix_Bi_Func_1_object_NatTrans : NatTrans (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G' F) :=
    {|
      Trans := fun c => (F @_a (G, c) (G', c) (N, id))%morphism
    |}.

  Next Obligation.
  Proof.
    intros c c' h.
    cbn.
    repeat rewrite <- F_compose.
    cbn.
    rewrite NatTrans_id_unit_left, NatTrans_id_unit_right.
    auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Fix_Bi_Func_1_object_NatTrans_obligation_1.
  Qed.

End Fix_Bi_Func_1_object_NatTrans.

Section Fix_Bi_Func_1_object_NatIso.
  Context {B C D E : Category} (F : Functor (Prod_Cat (Func_Cat C D) B) E)
          {G G' : Functor C D} (N : (G ≡≡ G' ::> Func_Cat _ _)%morphism).

  Program Definition Fix_Bi_Func_1_object_NatIso : ((@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G F) ≡≡ (@Fix_Bi_Func_1 (Func_Cat _ _) _ _ G' F) ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := Fix_Bi_Func_1_object_NatTrans F (iso_morphism N);
      inverse_morphism := Fix_Bi_Func_1_object_NatTrans F (inverse_morphism N)
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    rewrite <- F_compose; cbn.
    cbn_rewrite (left_inverse N).
    simpl_ids.
    change (NatTrans_id G, id) with (id (Prod_Cat (Func_Cat _ _) B) (G, c)).
    auto.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    rewrite <- F_compose; cbn.
    cbn_rewrite (right_inverse N).
    simpl_ids.
    change (NatTrans_id G', id) with (id (Prod_Cat (Func_Cat _ _) B) (G', c)).
    auto.
  Qed.

End Fix_Bi_Func_1_object_NatIso.

Section Fix_Bi_Func_2_object_NatTrans.
  Context {B C D E : Category} (F : Functor (Prod_Cat B (Func_Cat C D)) E)
          {G G' : Functor C D} (N : NatTrans G G').

  Program Definition Fix_Bi_Func_2_object_NatTrans : NatTrans (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G' F) :=
    {|
      Trans := fun c => (F @_a (c, G) (c, G') (id, N))%morphism
    |}.

  Next Obligation.
  Proof.
    intros c c' h; cbn.
    repeat rewrite <- F_compose; cbn.
    rewrite NatTrans_id_unit_left, NatTrans_id_unit_right.
    auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Fix_Bi_Func_2_object_NatTrans_obligation_1.
  Qed.

End Fix_Bi_Func_2_object_NatTrans.

Section Fix_Bi_Func_2_object_NatIso.
  Context {B C D E : Category} (F : Functor (Prod_Cat B (Func_Cat C D)) E)
          {G G' : Functor C D} (N : (G ≡≡ G' ::> Func_Cat _ _)%morphism).

  Program Definition Fix_Bi_Func_2_object_NatIso : ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G F) ≡≡ (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ G' F) ::> Func_Cat _ _)%morphism :=
    {|
      iso_morphism := Fix_Bi_Func_2_object_NatTrans F (iso_morphism N);
      inverse_morphism := Fix_Bi_Func_2_object_NatTrans F (inverse_morphism N)
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    rewrite <- F_compose; cbn.
    simpl_ids.
    cbn_rewrite (left_inverse N).
    change (id, NatTrans_id G) with (id (Prod_Cat B (Func_Cat _ _)) (c, G)).
    auto.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    rewrite <- F_compose; cbn.
    simpl_ids.
    cbn_rewrite (right_inverse N).
    change (id, NatTrans_id G') with (id (Prod_Cat B (Func_Cat _ _)) (c, G')).
    auto.
  Qed.

End Fix_Bi_Func_2_object_NatIso.