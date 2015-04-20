Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.Main.

Local Notation hcomp := NatTrans_hor_comp (only parsing).

Notation Hom_Adj_Left C D F G := (Functor_compose (Prod_Functor (Opposite_Functor F) (@Functor_id D)) (Hom_Func D)) (only parsing).
Notation Hom_Adj_Right C D F G := (Functor_compose (Prod_Functor (@Functor_id C^op) G) (Hom_Func C)) (only parsing).

Local Obligation Tactic := idtac.

Section Adjunction.
  Context {C D : Category} (F : Functor C D) (G : Functor D C).

  Class Adjunct : Type :=
  {
    adj_unit : NatTrans (@Functor_id C) (Functor_compose F G);
    adj_morph_ex {c : C} {d : D} (f : Hom c (G _o d)) : Hom (F _o c) d;
    adj_morph_com {c : C} {d : D} (f : Hom c (G _o d)) : f = (G _a _ _ (adj_morph_ex f)) ∘ (Trans adj_unit c);
    adj_morph_unique {c : C} {d : D} (f : Hom c (G _o d)) (g h : Hom (F _o c) d) :
      f = (G _a _ _ g) ∘ (Trans adj_unit c) → f = (G _a _ _ h) ∘ (Trans adj_unit c) → g = h
  }.

  Arguments adj_unit : clear implicits.
  Arguments adj_morph_ex _ {_ _} _.
  Arguments adj_morph_com _ {_ _} _.
  Arguments adj_morph_unique _ {_ _} _ _ _ _ _.

  Definition Hom_Adjunct := Hom_Adj_Left _ _ F G ≡≡ Hom_Adj_Right _ _ F G ::> Func_Cat _ _.

  Existing Class Hom_Adjunct.
  
  Section Adj_Hom_Adj.
    Context (Adj : Adjunct).

    Program Instance Adj_to_Hom_Adj_LR : NatTrans (Hom_Adj_Left _ _ F G) (Hom_Adj_Right _ _ F G) :=
    {
      Trans := fun c h => (G _a _ _ h) ∘ (Trans (adj_unit Adj) _)
    }.

    Next Obligation. (* Trans_com *)
      intros [c1 d1] [c2 d2] [h1 h2].
      extensionality x; cbn in *.
      repeat rewrite F_compose.
      change (G _a _ _ (F _a _ _ h1)) with ((Functor_compose F G) _a _ _ h1).
      repeat rewrite assoc.
      repeat refine (@f_equal _ _ (fun x => @compose _ _ _ _ x _) _ _ _).
      apply (eq_sym (Trans_com (adj_unit Adj) h1)).
    Qed.

    Next Obligation. (* Trans_com *)
    Proof.
      symmetry.
      apply Adj_to_Hom_Adj_LR_obligation_1.
    Qed.
    
    Program Instance Adj_to_Hom_Adj_RL : NatTrans (Hom_Adj_Right _ _ F G) (Hom_Adj_Left _ _ F G) :=
    {
      Trans := fun c h => adj_morph_ex Adj h
    }.

    Next Obligation.
      intros [c1 d1] [c2 d2] [h1 h2].
      extensionality x; cbn in *.
      eapply adj_morph_unique; eauto.
      simpl_ids.
      rewrite <- adj_morph_com.
      repeat rewrite F_compose.
      repeat rewrite assoc.
      refine (@f_equal _ _ (fun x => @compose _ _ _ _ x _) _ _ _).
      change (G _a _ _ (F _a _ _ h1)) with ((Functor_compose F G) _a _ _ h1).
      refine (eq_trans _ (@f_equal _ _ (fun x => @compose _ _ _ _ x _) _ _ (Trans_com (adj_unit Adj) h1))).
      rewrite assoc_sym.
      rewrite <- adj_morph_com; trivial.
    Qed.

    Next Obligation. (* Trans_com *)
    Proof.
      symmetry.
      apply Adj_to_Hom_Adj_RL_obligation_1.
    Qed.

    Program Instance Adj_to_Hom_Adj : Hom_Adjunct := NatIso _ _ Adj_to_Hom_Adj_LR Adj_to_Hom_Adj_RL _ _.
    
    Next Obligation.
      intros [c d].
      cbn in *.
      extensionality x.
      apply (eq_trans (eq_sym (adj_morph_com _ _))); auto.
    Qed.

    Next Obligation.
      intros [c d].
      extensionality x; cbn in *.
      eapply adj_morph_unique; eauto.
      rewrite <- adj_morph_com; trivial.
    Qed.

  End Adj_Hom_Adj.


  Section Hom_Adj_Adj.
    Context (Adj : Hom_Adjunct).

    Program Instance Hom_Adj_to_Adj : Adjunct :=
      {
        adj_unit := {| Trans := fun c => Trans (iso_morphism Adj) (c, F _o c) id |};
        adj_morph_ex := fun _ _ f => Trans (inverse_morphism Adj) (_, _) f
      }.
    
    Next Obligation.
      intros c c' h.
      set (H := @equal_f _ _ _ _ (@Trans_com _ _ _ _ (iso_morphism Adj) (c', F _o c') (c, F _o c') (h, id)) id).
      set (H' := (@equal_f _ _ _ _ (@Trans_com _ _ _ _ (iso_morphism Adj) (c, F _o c) (c, F _o c') (id c, F _a _ _ h)) id)).
      cbn in *.
      rewrite F_id in H.
      rewrite F_id in H'.
      simpl_ids in H.
      simpl_ids in H'.
      rewrite <- H; trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Hom_Adj_to_Adj_obligation_1.
    Qed.

    Next Obligation.
      intros c d f.
      cbn.
      set (H := @equal_f _ _ _ _ (@Trans_com _ _ _ _ (iso_morphism Adj) (c, F _o c) (c, d) (id, Trans (inverse_morphism Adj) (c, d) f)) id); cbn in H.
      rewrite F_id in H.
      simpl_ids in H.
      etransitivity; [|eassumption].
      change (f = Trans (NatTrans_compose (inverse_morphism Adj) (iso_morphism Adj)) (_, _) f).
      set (H' := right_inverse Adj); cbn in H'.
      rewrite H'.
      cbn; auto.
    Qed.

    Next Obligation.
      intros c d f g h H1 H2.
      cbn in *.
      cut (Trans (NatTrans_compose (iso_morphism Adj) (inverse_morphism Adj)) (_, _) g = Trans (NatTrans_compose (iso_morphism Adj) (inverse_morphism Adj)) (_, _) h); [intros H'|].
      + set (H'' := left_inverse Adj); cbn in H''.
        rewrite H'' in H'.
        cbn in H'; auto.
      + set (Hg := @equal_f _ _ _ _ (@Trans_com _ _ _ _ (iso_morphism Adj) (c, F _o c) (c, d) (id, g)) id); cbn in Hg; rewrite F_id in Hg; simpl_ids in Hg.
        set (Hh := @equal_f _ _ _ _ (@Trans_com _ _ _ _ (iso_morphism Adj) (c, F _o c) (c, d) (id, h)) id); cbn in Hh; rewrite F_id in Hh; simpl_ids in Hh.
        cbn.
        rewrite Hg, Hh; rewrite <- H1, <- H2; trivial.
    Qed.        

  End Hom_Adj_Adj.

End Adjunction.

Arguments adj_unit {_ _ _ _} _ : assert.
Arguments adj_morph_ex {_ _ _ _} _ {_ _} _.
Arguments adj_morph_com {_ _ _ _} _ {_ _} _.
Arguments adj_morph_unique {_ _ _ _} _ {_ _} _ _ _ _ _.

Arguments Adj_to_Hom_Adj {_ _ _ _} _.

Arguments Hom_Adj_to_Adj {_ _ _ _} _.

