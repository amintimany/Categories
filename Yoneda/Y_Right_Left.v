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

Program Instance Y_right_to_left_NT (C : Category) (c : Obj) (F : Functor C ^op Type_Cat) (h : F _o c) : NatTrans (Yoneda_emb_O _ c) F :=
{
  Trans := fun c' => fun g => (F _a _ _ g) h
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C c F h c1 c2 h'.
  extensionality g; simpl.
  match goal with
      [|- ?F _a _ _ (?X ∘ ?Y) ?Z = _] =>
      transitivity (((F _a _ _ Y) ∘ (F _a _ _ X)) Z); trivial
  end.
  rewrite <- F_compose; trivial.
Qed.

Program Instance Y_right_to_left (C : Category) : NatTrans (Y_right C) (Y_left C) :=
{
  Trans := fun c_F => fun h => Y_right_to_left_NT C (fst c_F) (snd c_F) h
}.

Next Obligation. (* Trans_com *)
Proof.
  intros C [c f] [c' f'] [h N].
  simpl in *.
  extensionality g; simpl.
  apply NatTrans_eq_simplify.
  extensionality d; extensionality g'; simpl.
  match goal with
      [|- ?F _a _ _ ?X (?F _a _ _ ?Y ?Z) = _] =>
      transitivity (((F _a _ _ X) ∘ (F _a _ _ Y)) Z); trivial
  end.
  rewrite <- F_compose; simpl.
  match goal with
      [|- ?X (?Y ?Z) = _] =>
      transitivity ((X ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; simpl; trivial.
Qed.  



