Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Representable.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.

Local Obligation Tactic := idtac.

Program Instance Y_right `(C : Category Obj Hom) : Functor (Prod_Cat C ^op (Func_Cat C ^op Type_Cat)) Type_Cat :=
{
  FO := fun x => (snd x) _o (fst x);
  FA := fun x y f => ((snd y) _a _ _ (fst f)) ∘ (@Trans _ _ _ _ _ _ _ _ (snd f) (fst x))
}. 

Next Obligation. (* F_id *)
Proof.
  intros Obj Hom C [c f].
  simpl.
  extensionality x.
  repeat rewrite (@F_id _ _ C ^op _ _ Type_Cat f).
  reflexivity.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros Obj Hom C [? ?] [? ?] [? ?] [? ?] [? ?].
  simpl in *.
  extensionality x.
  match goal with
      [|- ?F _a _ _ ?X ?Z = _] =>
      match X with
          (?U ∘ ?V) =>
          let H := fresh "H" in
          let H1 := fresh "H" in
          assert (H : F _a _ _ X = ((F _a _ _ V) ∘ (F _a _ _ U))); [rewrite <- F_compose; f_equal|];
          transitivity (((F _a _ _ V) ∘ (F _a _ _ U)) Z); [apply equal_f; trivial|]; clear H
      end
  end.
  simpl.
  f_equal.
  match goal with
      [|- ?X (?Y ?Z) = _] =>
      transitivity ((fun x => (X ∘ Y) x) Z); trivial
  end.
  rewrite <- Trans_com; trivial.
Qed.

(* Y_left defined *)



