(**
    This file contains the definition of Hom functor, Yoneda Embeding, Yoneda Lemma, etc.
*)

Require Import Category.Core.
Require Import Functor.Core.
Require Import Coq_Cats.Type_Cat.
Require Import Ext_Cons.Core.
Require Import NatTrans.NatTrans.


Local Obligation Tactic := (unfold HOM in * || idtac); program_simpl; auto.

Program Instance Hom_Func `(C : Category Obj Hom) : Functor (Prod_Cat C ^op C) Type_Cat :=
{
  FO := fun x => Hom (fst x) (snd x);
  FA := fun x y f => fun g => (@compose _ _ C _ _ _) (fst f) ((snd f) ∘ g)
}.

(* Hom_Func defined *)

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


Program Instance Y_right `(C : Category Obj) : Functor (Prod_Cat C ^op (Func_Cat C ^op Type_Cat)) Type_Cat :=
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

Program Instance Y_left_to_right `(C : Category Obj) : NatTrans (Y_left C) (Y_right C) :=
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

Program Instance Y_right_to_left_NT `(C : Category Obj) (c : Obj) (F : Functor C ^op Type_Cat) (h : F _o c) : NatTrans (Yoneda_emb_O _ c) F :=
{
  Trans := fun c' => fun g => (F _a _ _ g) h
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros Obj Hom C c F h c1 c2 h'.
  extensionality g; simpl.
  match goal with
      [|- ?F _a _ _ (?X ∘ ?Y) ?Z = _] =>
      transitivity (((F _a _ _ Y) ∘ (F _a _ _ X)) Z); trivial
  end.
  rewrite <- F_compose.
  trivial.
Qed.

Program Instance Y_right_to_left `(C : Category Obj) : NatTrans (Y_right C) (Y_left C) :=
{
  Trans := fun c_F => fun h => Y_right_to_left_NT _ (fst c_F) (snd c_F) h
}.

Next Obligation. (* Trans_com *)
Proof.
  intros Obj Hom C [c f] [c' f'] [h N].
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

Instance Yoneda_Embedding `(C : Category Obj Hom) : Embedding (Yoneda_emb C) :=
{
  F_Faithful := Yoneda_Faithful C;
  F_Full := Yoneda_Full C
}.

Theorem Yoneda_Iso `(C : Category Obj Hom) : forall (c c' : Obj), (Yoneda_emb C) _o c ≡ (Yoneda_emb C) _o c' -> c ≡ c'.
Proof.
  apply (@F_Guarantees_Isos _ _ _ _ _ _ (Yoneda_emb C) _).
Qed.

Ltac Yoneda := apply Yoneda_Iso.

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




