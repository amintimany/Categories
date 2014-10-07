Require Import Category.Core.

Class PreOrder : Type :=
{
  PreOrder_car : Type;
  
  PreOrder_rel : PreOrder_car → PreOrder_car → Prop;

  PreOrder_refl : ∀ a, PreOrder_rel a a;

  PreOrder_trans : ∀ a b c, PreOrder_rel a b → PreOrder_rel b c → PreOrder_rel a c
}.

Section PreOrder_Cat.
  Context (P : PreOrder).

  Inductive PreOrder_Hom (a b : @PreOrder_car P) : Type :=
  | PreOrder_Arrow : PreOrder_rel a b → PreOrder_Hom a b
  .

  Hint Constructors PreOrder_Hom.

  Hint Extern 1 =>
  match goal with
      [H : PreOrder_Hom _ _ |- _] =>
      destruct H; simpl in *
  end.

  Hint Extern 1 =>
  match goal with
      [|- PreOrder_Arrow ?A ?B ?H1 = PreOrder_Arrow ?A ?B ?H2] =>
      progress destruct (proof_irrelevance _ H1 H2)
  end.

  Hint Extern 1 =>
  match goal with
      [|- PreOrder_Arrow ?A ?B ?H1 = PreOrder_Arrow ?A ?B ?H2] =>
      progress destruct (proof_irrelevance _ H2 H1)
  end.

  Hint Resolve PreOrder_refl PreOrder_trans.

  Local Obligation Tactic := program_simpl; eauto.

  Program Instance PreOrder_Cat : Category (@PreOrder_car P) (PreOrder_Hom).

End PreOrder_Cat.