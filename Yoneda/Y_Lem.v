Require Import Category.Main.
Require Import Functor.Main.
Require Import Functor.Representable.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Require Import Yoneda.Y_emb.
Require Import Yoneda.Y_Left.
Require Import Yoneda.Y_Right.
Require Import Yoneda.Y_Left_Right.
Require Import Yoneda.Y_Right_Left.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

Lemma Yoneda_Lemma `(C : Category Obj Hom) : (Y_left C) ≡ (Y_right C).
Proof.
  apply NatIso with (n := Y_left_to_right C) (n' := Y_right_to_left C);
    intros [c F]; extensionality x; simpl in *.
  {  
    repeat rewrite (@F_id _ _ _ _ _ _ F); reflexivity.
  }
  {
    apply NatTrans_eq_simplify.
    extensionality c'; extensionality h.
    simpl in *.
    match goal with
      [|- ?X (?Y ?Z) = _] =>
      transitivity ((X ∘ Y) Z); trivial
    end.
    rewrite <- Trans_com.
    rewrite (@F_id _ _ _ _ _ _ F).
    trivial.
  }
Qed.

Lemma Yoneda_Faithful `(C : Category Obj Hom) : Faithful_Func (Yoneda_emb C).
Proof.
  intros c c' f f' H.
  simpl in *.
  match type of H with
      ?X = ?Y =>
      assert(H' : Trans X c id= Trans Y c id)
  end.
  rewrite H; trivial.
  simpl in H'.
  simpl_ids in H'.
  trivial.
Qed.

Lemma Yoneda_Full `(C : Category Obj Hom) : Full_Func (Yoneda_emb C).
Proof.
  intros c c' N.
  exists (Trans (Y_left_to_right C) (c, (((Yoneda_emb C) _o) c')) N).
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h.
  simpl in *.
  transitivity (((Yoneda_emb_O C c') _a _ _ h ∘ (Trans N c)) id).
  reflexivity.
  rewrite <- Trans_com.
  simpl.
  simpl_ids.
  trivial.
Qed.

Instance Yoneda_Embedding `(C : Category Obj Hom) : Embedding C (Func_Cat C ^op Type_Cat) :=
{
  Embedding_Func := Yoneda_emb C;
  F_Faithful := Yoneda_Faithful C;
  F_Full := Yoneda_Full C
}.

Theorem Yoneda_Iso `(C : Category Obj Hom) : forall (c c' : Obj), (Yoneda_emb C) _o c ≡ (Yoneda_emb C) _o c' -> c ≡ c'.
Proof.
  intros.
  apply (@F_Guarantees_Isos _ _ _ _ _ _ (Yoneda_Embedding C) _); trivial.
Qed.

Ltac Yoneda := apply Yoneda_Iso.



