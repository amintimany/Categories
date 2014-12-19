Require Import Category.Main.
Require Import Functor.Functor.
Require Import Cat.Cat.
Require Import Cat.Cat_Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Basic_Cons.CCC.
Require Import Coq_Cats.Type_Cat.Type_Cat_CCC.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

Program Instance Hom_Func (C : Category) : Functor ((@Prod_Func Cat _) _o (C^op, C)) Type_Cat :=
{
  FO := fun x => @Hom C (fst x) (snd x);
  FA := fun x y f => fun g => (@compose C _ _ _) (fst f) ((@compose C^op _ _ _) (snd f) g)
}.

Next Obligation. (* F_id *)
  intros C c.
  extensionality x.
  simpl; auto.
Qed.

Next Obligation. (* F_compose *)
  intros C a b c f g.
  extensionality x.
  simpl; abstract auto.
Qed.

(* Hom_Func defined *)





