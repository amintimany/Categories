Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Nat_Facts Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.Main.
Require Import Adjunction.Adjunction Adjunction.Duality.
Require Import Cat.Cat Cat.Cat_Exponential Cat.Cat_Exponential_Facts.
Require Import Yoneda.Yoneda.
Require Import Functor.Functor_Extender.

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

Section Hom_Adjunct_Lifted.
  Context {C D : Category} {F : Functor C D} {G : Functor D C} (adj : UCU_Adjunct F G) (B : Category).

  Local Notation FCOMP := Functor_compose (only parsing).
  Local Notation FOP := Opposite_Functor (only parsing).
  Local Notation NCOMP := NatTrans_compose (only parsing).
  Local Notation HCOMP := NatTrans_hor_comp (only parsing).
  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).

  Local Notation LEFT := (FCOMP (Prod_Functor (Opposite_Functor (Right_Functor_Extender F B)) (Functor_id (Func_Cat B D))) (Hom_Func (Func_Cat B D))) (only parsing).

  Local Notation RIGHT := (FCOMP (Prod_Functor (Functor_id (Func_Cat B C)^op) (Right_Functor_Extender G B)) (Hom_Func (Func_Cat B C))) (only parsing).

  Local Obligation Tactic := idtac.
  
  Program Instance Hom_Adjunct_Lifted_LR : NatTrans LEFT RIGHT :=
    {
      Trans := fun c h =>
                 NCOMP (NatTrans_to_compose_id _) (NCOMP (NCOMP (HCOMP (NatTrans_id (fst c)) (ucu_adj_unit adj)) (NatTrans_Functor_assoc (fst c) F G)) (HCOMP h (NatTrans_id G)))
    }.

  Next Obligation.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality w.
    apply NatTrans_eq_simplify.
    extensionality x.
    cbn in *.
    repeat rewrite F_id; simpl_ids.
    repeat rewrite F_compose.
    set (W := @Trans_com _ _ _ _ (ucu_adj_unit adj) _ _ (Trans h1 x)).
    cbn in W.
    repeat rewrite assoc.
    rewrite W.
    trivial.
  Qed.    

  Next Obligation.
    symmetry.
    apply Hom_Adjunct_Lifted_LR_obligation_1.
  Qed.

  Program Instance Hom_Adjunct_Lifted_RL : NatTrans RIGHT LEFT :=
    {
      Trans := fun c h => NCOMP (NCOMP (HCOMP h (NatTrans_id F)) (NCOMP (NatTrans_Functor_assoc_sym (snd c) G F) (HCOMP (NatTrans_id (snd c)) (ucu_adj_counit adj)))) (NatTrans_from_compose_id _)
    }.
    
  Next Obligation.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality w.
    apply NatTrans_eq_simplify.
    extensionality x.
    cbn in *.
    repeat rewrite F_id; simpl_ids.
    repeat rewrite F_compose.
    set (W := @Trans_com _ _ _ _ (ucu_adj_counit adj) _ _ (Trans h2 x)).
    cbn in W.
    repeat rewrite assoc_sym.
    rewrite <- W.
    trivial.
  Qed.    

  Next Obligation.
    symmetry.
    apply Hom_Adjunct_Lifted_RL_obligation_1.
  Qed.

  Program Instance Hom_Adjunct_Lifted : LEFT ≡≡ RIGHT ::> Func_Cat _ _ :=
    {
      iso_morphism := Hom_Adjunct_Lifted_LR;
      inverse_morphism := Hom_Adjunct_Lifted_RL
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify;
    extensionality c; extensionality h.
    destruct c as [c1 c2].
    apply NatTrans_eq_simplify; extensionality y.
    cbn in *.
    repeat rewrite F_id.
    simpl_ids.
    rewrite F_compose.
    rewrite assoc_sym.
    set (W := Trans_com (ucu_adj_counit adj) (Trans h y)); cbn in W; rewrite W; clear W.
    rewrite assoc.
    simpl_ids; trivial.
    set (W := f_equal (fun w : NatTrans F F => Trans w (c1 _o y)) (ucu_adj_left_id adj)); cbn in W; simpl_ids in W; apply W.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify;
    extensionality c; extensionality h.
    destruct c as [c1 c2].
    apply NatTrans_eq_simplify; extensionality y.
    cbn in *.
    repeat rewrite F_id.
    simpl_ids.
    rewrite F_compose.
    rewrite assoc.
    set (W := Trans_com (ucu_adj_unit adj) (Trans h y)); cbn in W; rewrite <- W; clear W.
    rewrite assoc_sym.
    simpl_ids; trivial.
    set (W := f_equal (fun w : NatTrans G G => Trans w (c2 _o y)) (ucu_adj_right_id adj)); cbn in W;
    repeat rewrite F_compose in W; repeat rewrite F_id in W; simpl_ids in W; apply W.
  Qed.

End Hom_Adjunct_Lifted.