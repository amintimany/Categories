Require Import Category.Main.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Yoneda_emb_O (C : Category) (c : Obj) : Functor C^op Type_Cat :=
{
  FO := fun x => @Hom C x c;
  FA := fun x y f => fun g => (@compose C _ _ _) f g
}.

Program Instance Yoneda_emb_A (C : Category) (x y : Obj) (f : Hom x y) : NatTrans (Yoneda_emb_O _ x) (Yoneda_emb_O _ y) :=
{
  Trans := fun c => fun g => f ∘ g
}.

Program Instance Yoneda_emb (C : Category) : Functor C (Func_Cat C ^op Type_Cat) :=
{
  FO := fun x => Yoneda_emb_O _ x;
  FA := fun x y f => Yoneda_emb_A _ x y f
}.

Next Obligation. (* F_id *)
Proof.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality f.
  simpl; auto.
Qed.

Next Obligation. (* F_compose *)
Proof.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h.
  simpl; auto.
Qed.

(* Yoneda_emb defined *)


