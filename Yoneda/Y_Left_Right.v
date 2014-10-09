Require Import Category.Core.
Require Import Functor.Functor.
Require Import Functor.Representable.Core.
Require Import Coq_Cats.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.
Require Import Yoneda.Y_Left.
Require Import Yoneda.Y_Right.

Local Obligation Tactic := idtac.

Program Instance Y_left_to_right `(C : Category Obj Hom) : NatTrans (Y_left C) (Y_right C) :=
{
  Trans := fun c_F => fun N => ((Trans N (fst c_F))) (@id _ _ _ (fst c_F))
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros Obj Hom C [c F] [c' F'] [h1 h2].
  extensionality N; simpl.
  simpl in *.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; simpl.
  f_equal.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; simpl.
  f_equal.
  auto.
Qed.



