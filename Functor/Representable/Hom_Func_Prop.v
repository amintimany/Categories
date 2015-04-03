Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Representable.Hom_Func.
Require Import Cat.Cat Cat.Cat_Iso.
Require Import NatTrans.NatTrans.

Section Hom_Func_Twist.
  Context (C : Category).
  
  Theorem Hom_Func_Twist : (Hom_Func C^op) = Functor_compose (Twist_Func C C^op) (Hom_Func C).
  Proof.
    Functor_extensionality c c' f.
    trivial.
    cbn; auto.
  Qed.

End Hom_Func_Twist.

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