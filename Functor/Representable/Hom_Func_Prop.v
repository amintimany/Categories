Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Representable.Hom_Func.
Require Import Cat.Cat Cat.Cat_Iso.
Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.

Section Hom_Func_Twist.
  Context (C : Category).
  
  Theorem Hom_Func_Twist : (Hom_Func C^op) = Functor_compose (Twist_Func C C^op) (Hom_Func C).
  Proof.
    match goal with
      [|- ?A = ?B] =>
      set (Oeq := eq_refl : A _o = B _o); apply (Functor_eq_simplify _ _ Oeq)
    end.    
    extensionality x; extensionality y; extensionality f; extensionality g.
    cbn; auto.
  Qed.

End Hom_Func_Twist.

Section Prod_Func_Hom_Func_NT.
  Context {A B C D : Category} {F : Functor A C^op} {F' : Functor A D^op} {G : Functor B C} {G' : Functor B D} (N : NatTrans (Functor_compose (Prod_Functor F G) (Hom_Func C)) (Functor_compose (Prod_Functor F' G') (Hom_Func D))).

  Local Obligation Tactic := idtac.
  
  Program Instance Prod_Func_Hom_Func_NT : NatTrans (Functor_compose (Prod_Functor G F) (Hom_Func C^op)) (Functor_compose (Prod_Functor G' F') (Hom_Func D^op)) :=
    {
      Trans := fun c h => Trans N (snd c, fst c) h
    }.

  Next Obligation.
  Proof.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality x.
    set (W := equal_f (@Trans_com _ _ _ _ N (c2, c1) (c2', c1') (h2, h1)) x); cbn in W.
    repeat rewrite assoc in W.
    trivial.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Prod_Func_Hom_Func_NT_obligation_1.
  Qed.

End Prod_Func_Hom_Func_NT.
  
Section Prod_Func_Hom_Func.
  Context {A B C D : Category} {F : Functor A C^op} {F' : Functor A D^op} {G : Functor B C} {G' : Functor B D} (N : Functor_compose (Prod_Functor F G) (Hom_Func C) ≡≡ Functor_compose (Prod_Functor F' G') (Hom_Func D) ::> Func_Cat _ _).
  
  Program Instance Prod_Func_Hom_Func : Functor_compose (Prod_Functor G F) (Hom_Func C^op) ≡≡ Functor_compose (Prod_Functor G' F') (Hom_Func D^op) ::> Func_Cat _ _ :=
    {
      iso_morphism := Prod_Func_Hom_Func_NT (iso_morphism N);
      inverse_morphism := Prod_Func_Hom_Func_NT (inverse_morphism N)
    }.

  Next Obligation.
  apply NatTrans_eq_simplify; extensionality x; extensionality h.
  cbn in *.
  match goal with
    [|- ?W = _] =>
    match W with
      Trans ?A ?X (Trans ?B ?X ?Z) =>
      change W with (Trans (NatTrans_compose B A) X Z)
    end
  end.
  set (W := left_inverse N); cbn in W; rewrite W.
  trivial.
  Qed.

  Next Obligation.
  apply NatTrans_eq_simplify; extensionality x; extensionality h.
  cbn in *.
  match goal with
    [|- ?W = _] =>
    match W with
      Trans ?A ?X (Trans ?B ?X ?Z) =>
      change W with (Trans (NatTrans_compose B A) X Z)
    end
  end.
  set (W := right_inverse N); cbn in W; rewrite W.
  trivial.
  Qed.

End Prod_Func_Hom_Func.

Section Prod_Func_Hom_Func_invl.
  Context {A B C D : Category} {F : Functor A C^op} {F' : Functor A D^op} {G : Functor B C} {G' : Functor B D} (N : Functor_compose (Prod_Functor F G) (Hom_Func C) ≡≡ Functor_compose (Prod_Functor F' G') (Hom_Func D) ::> Func_Cat _ _).
  
  Theorem Prod_Func_Hom_Func_invl : N = Prod_Func_Hom_Func (Prod_Func_Hom_Func N).
  Proof.
    apply Isomorphism_eq_simplify; apply NatTrans_eq_simplify; extensionality x; trivial.
  Qed.    

End Prod_Func_Hom_Func_invl.

Local Obligation Tactic := idtac.

Section Hom_Func_to_Iso_Hom_Func.
  Context {C D : Category} (I : C ≡≡ D ::> Cat).

  Program Instance Hom_Func_to_Iso_Hom_Func : NatTrans (Hom_Func C) (Functor_compose (Prod_Functor (Opposite_Functor (iso_morphism I)) (iso_morphism I)) (Hom_Func D)) :=
    {
      Trans := fun c h => (iso_morphism I) _a _ _ h
    }.

  Next Obligation.
  Proof.
    intros [c1 c2] [c1' c2'] [h1 h2]; cbn in *.
    extensionality x.
    repeat rewrite F_compose.
    repeat rewrite conv_HomI_compose.
    repeat rewrite conv_HomI_I_inv_I; trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Hom_Func_to_Iso_Hom_Func_obligation_1.
  Qed.

  Program Instance Iso_Hom_Func_to_Hom_Func : NatTrans (Functor_compose (Prod_Functor (Opposite_Functor (iso_morphism I)) (iso_morphism I)) (Hom_Func D)) (Hom_Func C) :=
    {
      Trans := fun c h => Cat_Iso_conv_inv I ((inverse_morphism I) _a _ _ h)
    }.

  Next Obligation.
  Proof.
    intros [c1 c2] [c1' c2'] [h1 h2]; cbn in *.
    extensionality x.
    repeat rewrite F_compose.
    repeat rewrite Cat_Iso_conv_inv_compose.
    repeat rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Iso_Hom_Func_to_Hom_Func_obligation_1.
  Qed.

    
  Program Instance Hom_Func_Cat_Iso : (Hom_Func C) ≡≡ Functor_compose (Prod_Functor (Opposite_Functor (iso_morphism I)) (iso_morphism I)) (Hom_Func D) ::> Func_Cat _ _ :=
    {
      iso_morphism := Hom_Func_to_Iso_Hom_Func;
      inverse_morphism := Iso_Hom_Func_to_Hom_Func
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c; cbn.
    extensionality f.
    repeat rewrite F_id; simpl_ids.
    apply Cat_Iso_conv_inv_I_inv_I.
  Qed.    

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c; cbn.
    extensionality f.
    repeat rewrite F_id; simpl_ids.
    destruct (Cat_Iso_inv I f) as [g H].
    rewrite H.
    rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.
  
End Hom_Func_to_Iso_Hom_Func.