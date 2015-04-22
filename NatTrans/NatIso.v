Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.Operations.

Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

Section NatIso.
  Context {C C' : Category} (F G : Functor C C') (n : NatTrans F G) (n' : NatTrans G F).

  Theorem NatIso : (∀ (c : Obj), (Trans n c) ∘ (Trans n' c) = (@id _ (G _o c))) →
                   (∀ (c : Obj), (Trans n' c) ∘ (Trans n c) = (@id _ (F _o c))) →
                   F ≡≡ G ::> Func_Cat _ _.
  Proof.
    intros H1 H2.
    apply (Build_Isomorphism (Func_Cat _ _) _ _ n n'); auto.
  Qed.

End NatIso.

Section NatTrans_id_Iso.
  Context {C D : Category} (F : Functor C D).

  Program Instance NatTrans_id_Iso : F ≡≡ F ::> Func_Cat _ _ :=
    {
      iso_morphism := NatTrans_id _;
      inverse_morphism := NatTrans_id _
    }.

End NatTrans_id_Iso.

Section NatIso_hor_comp.
  Context {C D E : Category} {F F' : Functor C D} {G G' : Functor D E} (N : F ≡≡ F' ::> Func_Cat _ _) (N' : G ≡≡ G' ::> Func_Cat _ _).

  Local Obligation Tactic := idtac.

  Program Instance NatIso_hor_comp : Functor_compose F G ≡≡ Functor_compose F' G' ::> Func_Cat _ _ :=
    {
      iso_morphism := NatTrans_hor_comp (iso_morphism N) (iso_morphism N');
      inverse_morphism := NatTrans_hor_comp (inverse_morphism N) (inverse_morphism N')
    }.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    set (H := left_inverse N); cbn in H; rewrite H; clear H.
    set (H := left_inverse N'); cbn in H; rewrite H; clear H.
    auto.
  Qed.

  Next Obligation.
  Proof.
    cbn.
    rewrite NatTrans_comp_hor_comp.
    set (H := right_inverse N); cbn in H; rewrite H; clear H.
    set (H := right_inverse N'); cbn in H; rewrite H; clear H.
    auto.
  Qed.

End NatIso_hor_comp.

Section Opposite_NatIso.
  Context {C D : Category} {F G : Functor C D} (N : F ≡≡ G ::> Func_Cat _ _).

  Program Instance Opposite_NatIso : Opposite_Functor F ≡≡ Opposite_Functor G ::> Func_Cat _ _ :=
    {
      iso_morphism := (Opposite_NatTrans (inverse_morphism N));
      inverse_morphism := (Opposite_NatTrans (iso_morphism N))
    }.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change (NatTrans_compose (iso_morphism N) N⁻¹) with (N⁻¹ ∘ N).
    rewrite left_inverse.
    apply NatTrans_id_Op.
  Qed.

  Next Obligation.
  Proof.
    rewrite <- NatTrans_compose_Op.
    change (NatTrans_compose N⁻¹ (iso_morphism N)) with (N ∘ N⁻¹).
    rewrite right_inverse.
    apply NatTrans_id_Op.
  Qed.

End Opposite_NatIso.

Section NatIso_compose.
  Context {C D : Category} {F G H : Functor C D} (N : F ≡≡ G ::> Func_Cat _ _) (N' : G ≡≡ H ::> Func_Cat _ _).

  Local Obligation Tactic := idtac.

  Program Instance NatIso_compose : F ≡≡ H ::> Func_Cat _ _ :=
    {
      iso_morphism := (NatTrans_compose (iso_morphism N) (iso_morphism N'));
      inverse_morphism := (NatTrans_compose (inverse_morphism N') (inverse_morphism N))
    }.

  Next Obligation.
  Proof.
    change (NatTrans_compose (iso_morphism N) (iso_morphism N')) with (N' ∘ N).
    change (NatTrans_compose N'⁻¹ N⁻¹) with (N⁻¹ ∘ N'⁻¹).
    rewrite assoc.
    rewrite (assoc_sym N _ _).
    rewrite left_inverse.
    simpl_ids.
    apply left_inverse.
  Qed.

  Next Obligation.
  Proof.
    change (NatTrans_compose (iso_morphism N) (iso_morphism N')) with (N' ∘ N).
    change (NatTrans_compose N'⁻¹ N⁻¹) with (N⁻¹ ∘ N'⁻¹).
    rewrite assoc.
    rewrite (assoc_sym _ _ N).
    rewrite right_inverse.
    simpl_ids.
    apply right_inverse.
  Qed.

End NatIso_compose.

Section Embedding_mono.
  Context {C C' : Category} (F : Embedding C C') {B : Category}.

  Local Obligation Tactic := idtac.
  
  Section Embedding_mono_NT.
    Context (G G' : Functor B C) (H : Functor_compose G F ≡≡ Functor_compose G' F ::> Func_Cat _ _).
    
    Program Instance Embedding_mono_NT :  NatTrans G G' :=
      {
        Trans := fun c => proj1_sig (Emb_Full _ (Trans (iso_morphism H) c))
      }.

    Next Obligation.
      intros c c' h.
      apply (Emb_Faithful F).
      repeat rewrite F_compose.
      set (W := proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))); cbn in W; rewrite W; clear W.
      set (W := proj2_sig (Emb_Full _ (Trans (iso_morphism H) c'))); cbn in W; rewrite W; clear W.
      apply (@Trans_com _ _ _ _ (iso_morphism H) _ _ h).
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Embedding_mono_NT_obligation_1.
    Qed.

  End Embedding_mono_NT.

  Context (G G' : Functor B C) (H : Functor_compose G F ≡≡ Functor_compose G' F ::> Func_Cat _ _).
  
  Program Instance Embedding_mono : G ≡≡ G' ::> Func_Cat _ _  :=
    {
      iso_morphism := Embedding_mono_NT _ _ H;
      inverse_morphism := Embedding_mono_NT _ _ (Inverse_Isomorphism H)
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    apply (Emb_Faithful F).
    repeat rewrite F_compose.
    set (W := proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))); cbn in W; rewrite W; clear W.
    set (W := proj2_sig (Emb_Full _ (Trans (inverse_morphism H) c))); cbn in W; rewrite W; clear W.
    rewrite F_id.
    change (Trans (inverse_morphism H) c ∘Trans (iso_morphism H) c) with
    (Trans (NatTrans_compose (iso_morphism H) (inverse_morphism H)) c).
    set (W := left_inverse H); cbn in W; rewrite W; clear W.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    apply (Emb_Faithful F).
    repeat rewrite F_compose.
    set (W := proj2_sig (Emb_Full _ (Trans (iso_morphism H) c))); cbn in W; rewrite W; clear W.
    set (W := proj2_sig (Emb_Full _ (Trans (inverse_morphism H) c))); cbn in W; rewrite W; clear W.
    rewrite F_id.
    change (Trans (iso_morphism H) c ∘Trans (inverse_morphism H) c) with
    (Trans (NatTrans_compose (inverse_morphism H) (iso_morphism H)) c).
    set (W := right_inverse H); cbn in W; rewrite W; clear W.
    trivial.
  Qed.    

End Embedding_mono.

Section NatIso_Functor_assoc.
  Context {C1 C2 C3 C4 : Category} (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4).
  
  Program Instance NatIso_Functor_assoc : (Functor_compose F (Functor_compose G H)) ≡≡ (Functor_compose (Functor_compose F G) H) ::> Func_Cat _ _ :=
    {
      iso_morphism := NatTrans_Functor_assoc F G H;
      inverse_morphism := NatTrans_Functor_assoc_sym F G H
    }.

End NatIso_Functor_assoc.