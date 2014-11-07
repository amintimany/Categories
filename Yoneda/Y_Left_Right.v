Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Representable.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.
Require Import Yoneda.Y_Left.
Require Import Yoneda.Y_Right.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

Program Instance Y_left_to_right (C : Category) : NatTrans (Y_left C) (Y_right C) :=
{
  Trans := fun c_F => fun N => ((Trans N (fst c_F))) (@id _ (fst c_F))
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C [c F] [c' F'] [h1 h2].
  extensionality N; simpl.
  simpl in *.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; simpl.
  apply f_equal.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; simpl.
  apply f_equal.
  auto.
Qed.



