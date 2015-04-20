Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Nat_Facts Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.
Require Import Adjunction.Adjunction Adjunction.Duality.
Require Import Cat.Cat Cat.Cat_Exponential Cat.Cat_Exponential_Facts.
Require Import Yoneda.Yoneda.

Section Hom_Adjunct_left_iso.
  Context {C D : Category} {F F' : Functor C D} (N : F' ≡≡ F ::> Func_Cat _ _) {G : Functor D C} (adj : Hom_Adjunct F G).

  Definition Hom_Adjunct_left_iso : Hom_Adjunct F' G := NatIso_compose (NatIso_hor_comp (Prod_Functor_NatIso (Opposite_NatIso N) (NatTrans_id_Iso (Functor_id D))) (NatTrans_id_Iso (Hom_Func D))) adj.

End Hom_Adjunct_left_iso.

Section Hom_Adjunct_right_iso.
  Context {C D : Category} {F : Functor C D} {G G' : Functor D C} (N : G ≡≡ G' ::> Func_Cat _ _) (adj : Hom_Adjunct F G).

  Definition Hom_Adjunct_right_iso : Hom_Adjunct F G' := Hom_Adjunct_Duality (Hom_Adjunct_left_iso (Inverse_Isomorphism (Opposite_NatIso N)) (Hom_Adjunct_Duality adj)).

End Hom_Adjunct_right_iso.

Section Adjunct_left_iso.
  Context {C D : Category} (F F' : Functor C D) (N : F' ≡≡ F ::> Func_Cat _ _) (G : Functor D C) (adj : Adjunct F G).

  Definition Adjunct_left_iso : Adjunct F' G := Hom_Adj_to_Adj (Hom_Adjunct_left_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_left_iso.

Section Adjunct_right_iso.
  Context {C D : Category} (F : Functor C D) (G G' : Functor D C) (N : G ≡≡ G' ::> Func_Cat _ _) (adj : Adjunct F G).

  Definition Adjunct_right_iso : Adjunct F G' := Hom_Adj_to_Adj (Hom_Adjunct_right_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_right_iso.

Section Hom_Adjunct_left_unique.
  Context {C D : Category} {F F' : Functor C D} {G : Functor D C} (adj : Hom_Adjunct F G) (adj' : Hom_Adjunct F' G).

  Theorem Hom_Adjunct_left_unique : F ≡≡ F' ::> Func_Cat _ _.
  Proof.
    apply (@Opposite_NatIso _ _ (Opposite_Functor F) (Opposite_Functor F')).
    eapply (Embedding_mono (Yoneda_Emb D^op)).
    cbn; unfold Yoneda; cbn.
    do 2 rewrite <- Exp_Cat_morph_ex_compose.
    apply Inverse_Isomorphism in adj';
      set (equiv := Isomorphism_Compose adj adj'); clearbody equiv; clear adj adj'.
    apply Exp_Cat_morph_ex_Iso.
    assumption.
  Qed.    

End Hom_Adjunct_left_unique.

Section Hom_Adjunct_right_unique.
  Context {C D : Category} {F : Functor C D} {G G' : Functor D C} (adj : Hom_Adjunct F G) (adj' : Hom_Adjunct F G').

  Theorem Hom_Adjunct_right_unique : G ≡≡ G' ::> Func_Cat _ _.
  Proof.
    apply Hom_Adjunct_Duality in adj.
    apply Hom_Adjunct_Duality in adj'.
    apply (@Opposite_NatIso _ _ (Opposite_Functor G) (Opposite_Functor G')).
    apply (Hom_Adjunct_left_unique adj adj').
  Qed.

End Hom_Adjunct_right_unique.

Section Adjunct_left_unique.
  Context {C D : Category} {F F' : Functor C D} {G : Functor D C} (adj : Adjunct F G) (adj' : Adjunct F' G).

  Theorem Adjunct_left_unique : F ≡≡ F' ::> Func_Cat _ _.
  Proof.
    apply Adj_to_Hom_Adj in adj.
    apply Adj_to_Hom_Adj in adj'.
    apply Hom_Adjunct_left_unique; trivial.
  Qed.    

End Adjunct_left_unique.

Section Adjunct_right_unique.
  Context {C D : Category} {F : Functor C D} {G G' : Functor D C} (adj : Adjunct F G) (adj' : Adjunct F G').

  Theorem Adjunct_right_unique : G ≡≡ G' ::> Func_Cat _ _.
  Proof.
    apply Adj_to_Hom_Adj in adj.
    apply Adj_to_Hom_Adj in adj'.
    apply Hom_Adjunct_right_unique; trivial.
  Qed.

End Adjunct_right_unique.

Section Adjoint_Compose.
  Context {C D E : Category}
          {F : Functor C D} {G : Functor D C} (adj : Adjunct F G)
          {F' : Functor D E} {G' : Functor E D} (adj' : Adjunct F' G').
  
  Program Instance Adjunct_Compose : Adjunct (Functor_compose F F') (Functor_compose G' G) :=
    {
      adj_unit := {|Trans := fun c => (G _a _ _ (Trans (adj_unit adj') (F _o c))) ∘ (Trans (adj_unit adj) c) |};
      adj_morph_ex := fun _ _ f => adj_morph_ex adj' (adj_morph_ex adj f)
    }.

  Next Obligation.
  Proof.
    rewrite assoc.
    set (W := (Trans_com (adj_unit adj) h)); cbn in W; rewrite W; clear W.
    rewrite assoc_sym.
    set (W := f_equal (G _a _ _) (Trans_com (adj_unit adj') ((F _a) _ _ h)));
      cbn in W; rewrite F_compose in W; rewrite W.
    repeat rewrite F_compose.
    auto.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Adjunct_Compose_obligation_1.
  Qed.    

  Next Obligation.
  Proof.
    rewrite assoc_sym.
    set (W := f_equal (G _a _ _) (adj_morph_com adj' (adj_morph_ex adj f)));
      rewrite F_compose in W; cbn in W; rewrite <- W; clear W.
    apply (adj_morph_com adj f).
  Qed.    

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros c d f g h H1 H2.
    cbn in *.
    rewrite assoc_sym in H1, H2.
    rewrite <- F_compose in H1, H2.
    set (W := @adj_morph_unique _ _ _ _ adj _ _ f _ _ H1 H2).
    cbn in W.
    match type of W with
      ?A = ?B =>
      apply (@adj_morph_unique _ _ _ _ adj' _ _ A _ _ eq_refl W)
    end.
  Qed.

End Adjoint_Compose.