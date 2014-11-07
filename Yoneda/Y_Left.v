Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Representable.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

Program Instance Y_left (C : Category) : Functor (Prod_Cat C ^op (Func_Cat C ^op Type_Cat)) Type_Cat :=
{
  FO := fun x => (Hom_Func (Func_Cat _ _)) _o ((Yoneda_emb_O C (fst x)), (snd x));
  FA := fun x y f => (Hom_Func (Func_Cat _ _)) _a (_, _) (_, _) ((Yoneda_emb_A C _ _ (fst f)), snd f)
}. 

Next Obligation. (* F_id *)
Proof.
  intros C [c f].
  simpl.
  extensionality F.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality g.
  simpl.
  simpl_ids.
  rewrite (@F_id C^op Type_Cat f).
  reflexivity.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros C a b c f1 f2. 
  simpl.
  extensionality F.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality g.
  simpl.
  rewrite assoc; trivial.
Qed.

(* Y_left defined *)



