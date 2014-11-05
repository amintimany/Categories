Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.
Require Import Yoneda.Y_Left.
Require Import Yoneda.Y_Right.
Require Import Yoneda.Y_Left_Right.
Require Import Yoneda.Y_Right_Left.
Require Import Yoneda.Y_Lem.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

(* Defineing CoYoneda explicitly. This makes definition of natrual isomorphisms simpler! *)

Program Instance CoYoneda_emb_O `(C : Category Obj Hom) (c : Obj) : Functor C Type_Cat :=
{
  FO := fun x => Hom c x;
  FA := fun x y f => fun g => f ∘ g
}.

Next Obligation. (* F_id *)
Proof.
  intros Obj Hom C a b.
  exact (Yoneda_emb_O_obligation_1 _ _ (C ^op) a b).
Defined.

Next Obligation. (* F_compose *)
Proof.
  intros Obj Hom C a b c d f g.
  exact (Yoneda_emb_O_obligation_2 _ _ (C ^op) a b c d f g).
Defined.

Program Instance CoYoneda_emb_A `(C : Category Obj Hom) (x y : Obj) (f : Hom y x) : NatTrans (CoYoneda_emb_O _ x) (CoYoneda_emb_O _ y) :=
{
  Trans := fun c => fun g => g ∘ f
}.

Next Obligation. (* Trans_com *)
Proof.  
  intros Obj Hom C a b f c d g.
  exact (Yoneda_emb_A_obligation_1 _ _ (C ^op) a b f c d g).
Defined.

Program Instance CoYoneda_emb `(C : Category Obj Hom) : Functor C ^op (Func_Cat C Type_Cat) :=
{
  FO := fun x => CoYoneda_emb_O C x;
  FA := fun x y f => CoYoneda_emb_A C x y f
}.

Next Obligation. (* F_id *)
Proof.
  intros Obj Hom C c.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality g; simpl.
  auto.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros Obj Hom C a b c f g.
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h; simpl.
  auto.
Qed.

Theorem CoYoneda_Co_Yoneda `(C : Category Obj Hom) : Yoneda_emb C^op ≃ CoYoneda_emb C.
Proof.
  destruct C.
  match goal with
      [|- ?A ~= ?B] =>
      cutrewrite (A = B); trivial
  end.
  Functor_extensionality a b f; trivial.
Qed.  

Theorem CoYoneda_Iso `(C : Category Obj Hom) : forall (c c' : Obj), (CoYoneda_emb C) _o c ≡ (CoYoneda_emb C) _o c' -> c ≡ c'.
  intros c c' H.
  assert(H' := @CoIso _ _ C^op).
  destruct C.
  apply H'.
  apply Yoneda_Iso.
  trivial.
Qed.

Ltac CoYoneda := apply CoYoneda_Iso.




