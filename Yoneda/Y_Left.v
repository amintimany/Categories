Require Import Category.Core.
Require Import Functor.Functor.
Require Import Functor.Representable.Core.
Require Import Coq_Cats.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.

Local Obligation Tactic := idtac.

Program Instance Y_left `(C : Category Obj Hom) : Functor (Prod_Cat C ^op (Func_Cat C ^op Type_Cat)) Type_Cat :=
{
  FO := fun x => (Hom_Func _) _o ((Yoneda_emb_O _ (fst x)), (snd x));
  FA := fun x y f => (Hom_Func _) _a (_, _) (_, _) ((Yoneda_emb_A _ _ _ (fst f)), snd f)
}. 

Next Obligation. (* F_id *)
Proof.
  intros Obj Hom C [c f].
  simpl.
  extensionality F.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality g.
  simpl.
  simpl_ids.
  rewrite (@F_id _ _ C ^op _ _ Type_Cat f).
  reflexivity.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros Obj Hom C a b c f1 f2. 
  simpl.
  extensionality F.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality g.
  simpl.
  rewrite assoc; trivial.
Qed.

(* Y_left defined *)



