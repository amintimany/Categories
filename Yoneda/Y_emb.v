Require Import Category.Core.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Program Instance Yoneda_emb_O `(C : Category Obj Hom) (c : Obj) : Functor C ^op Type_Cat :=
{
  FO := fun x => Hom x c;
  FA := fun x y f => fun g => (@compose _ _ C _ _ _) f g
}.

Program Instance Yoneda_emb_A `(C : Category Obj Hom) (x y : Obj) (f : Hom x y) : NatTrans (Yoneda_emb_O _ x) (Yoneda_emb_O _ y) :=
{
  Trans := fun c => fun g => f ∘ g
}.

Program Instance Yoneda_emb `(C : Category Obj Hom) : Functor C (Func_Cat C ^op Type_Cat) :=
{
  FO := fun x => Yoneda_emb_O _ x;
  FA := fun x y f => Yoneda_emb_A _ x y f
}.

Next Obligation. (* F_id *)
Proof.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality f.
  simpl.
  simpl_ids.
  trivial.
Qed.

Next Obligation. (* F_compose *)
Proof.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h.
  simpl; auto.
Qed.

(* Yoneda_emb defined *)


