Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Representable.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.

Local Obligation Tactic := idtac.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Y_right (C : Category) : Functor (Prod_Cat C ^op (Func_Cat C ^op Type_Cat)) Type_Cat :=
{
  FO := fun x => (snd x) _o (fst x);
  FA := fun x y f => ((snd y) _a _ _ (fst f)) ∘ (@Trans _ _ _ _ (snd f) (fst x))
}. 

Next Obligation. (* F_id *)
Proof.
  intros C [c f].
  simpl.
  extensionality x.
  repeat rewrite (@F_id C ^op Type_Cat f).
  reflexivity.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros C [? ?] [? ?] [? ?] [? ?] [? ?].
  simpl in *.
  extensionality x.
  match goal with
      [|- ?F _a _ _ ?X ?Z = _] =>
      match X with
          (?U ∘ ?V) =>
          let H := fresh "H" in
          let H1 := fresh "H" in
          cutrewrite (F _a _ _ X = ((F _a _ _ V) ∘ (F _a _ _ U)))
      end
  end.
  simpl.
  apply f_equal.
  match goal with
      [|- (?X (?Y ?Z)) = _] =>
      transitivity ((fun x => (X ∘ Y) x) Z); trivial
  end.
  rewrite <- Trans_com; trivial.
  rewrite <- F_compose; trivial.
Qed.

(* Y_left defined *)
