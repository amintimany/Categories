Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans.

Section Cat_IConv.
  Context {C D : Category} (I : C ≡≡ D ::> Cat).
  
  Definition Cat_Iso_Obj_conv (c : C) : c = (((inverse_morphism I) _o) (((iso_morphism I) _o) c)).
  Proof.
    change (I ⁻¹ _o ((iso_morphism I) _o c)) with ((I ⁻¹ ∘ I) _o c);
    rewrite (left_inverse I); trivial.
  Qed.
  
  Definition Cat_Iso_Hom_conv (c c' : C) : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c')) = Hom C c c'.
  Proof.
    do 2 rewrite <- Cat_Iso_Obj_conv; trivial.
  Defined.

  Definition Cat_Iso_conv_inv {c c' : C} (h : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))) : Hom C c c' :=
    match Cat_Iso_Hom_conv c c' in _ = Y return Y with
      eq_refl => h
    end.

  Theorem Cat_Iso_conv_inv_JMeq {c c' : C} (h : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))) : Cat_Iso_conv_inv h ~= h.
  Proof.
    unfold Cat_Iso_conv_inv.
    destruct Cat_Iso_Hom_conv.
    trivial.
  Qed.

  Definition Cat_Iso_conv {c c' : C} (h : Hom C c c') : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c')) :=
    match eq_sym (Cat_Iso_Hom_conv c c') in _ = Y return Y with
      eq_refl => h
    end.

  Theorem Cat_Iso_conv_JMeq {c c' : C} (h : Hom c c') : Cat_Iso_conv h ~= h.
  Proof.
    unfold Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv.
    trivial.
  Qed.
  
  Theorem Cat_Iso_conv_inv_Cat_Iso_conv {c c' : C} (h : Hom C c c') : Cat_Iso_conv_inv (Cat_Iso_conv h) = h.
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv; trivial.
  Qed.

  Theorem Cat_Iso_conv_Cat_Iso_conv_inv {c c' : C} (h : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))) : Cat_Iso_conv (Cat_Iso_conv_inv h) = h.
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv; trivial.
  Qed. 

  Theorem Cat_Iso_conv_inv_I_inv_I {c c' : C} (h : Hom C c c') : Cat_Iso_conv_inv (((inverse_morphism I) _a) _ _ (((iso_morphism I) _a) _ _ h)) = h.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      let H := fresh "H" in
      cut (A ~= B); [intros H; rewrite H; trivial|]
    end.
    unfold Cat_Iso_conv_inv.
    destruct Cat_Iso_Hom_conv.
    change (I ⁻¹ _a _ _ ((iso_morphism I) _a _ _ h)) with ((I ⁻¹ ∘ I) _a _ _ h).
    set (H := left_inverse I).
    cbn in H.
    apply (@JMeq_trans _ _ _ _ ((Functor_id _) _a _ _ h) _); trivial.
    rewrite <- H; trivial.
  Qed.
  
  Theorem Cat_Iso_conv_inv_compose {c c' c'' : C} (h : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c)) (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))) (h' : Hom (((inverse_morphism I) _o) (((iso_morphism I) _o) c')) (((inverse_morphism I) _o) (((iso_morphism I) _o) c''))) :
     Cat_Iso_conv_inv (compose C h h') = compose C (Cat_Iso_conv_inv h) (Cat_Iso_conv_inv h').
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_Hom_conv, eq_ind, eq_rect.
    do 3 destruct Cat_Iso_Obj_conv; trivial.
  Qed.

End Cat_IConv.

Section Cat_Iso_inv.
  Context {C D : Category} (I : C ≡≡ D ::> Cat).

  Theorem Cat_Iso_inv {c c' : C} (h : Hom D ((iso_morphism I) _o c) ((iso_morphism I) _o c')) : {g : Hom C c c' | h = ((iso_morphism I) _a _ _ g)}.
  Proof.
    exists (Cat_Iso_conv_inv I ((inverse_morphism I) _a _ _ h)).
    match goal with
      [|- ?A = ?B] =>
      let H := fresh "H" in
      let H' := fresh "H" in
      set (H := eq_sym (@Cat_Iso_conv_inv_I_inv_I D C (Inverse_Isomorphism I) _ _ A));
        set (H' := @Cat_Iso_conv_inv_I_inv_I D C (Inverse_Isomorphism I) _ _ B); cbn in H, H';
        etransitivity;
        [apply H|
         etransitivity; [|apply H']]; clear H; clear H'
    end.
    do 2 apply f_equal.
    match goal with
      [|- ?A = ?B] =>
      let H := fresh "H" in
      let H' := fresh "H" in
      set (H := eq_sym (@Cat_Iso_conv_Cat_Iso_conv_inv C D I _ _ A));
        set (H' := @Cat_Iso_conv_Cat_Iso_conv_inv C D I _ _ B); cbn in H, H';
        etransitivity;
        [apply H|
         etransitivity; [|apply H']]; clear H; clear H'
    end.
    apply f_equal.
    rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.

End Cat_Iso_inv.
