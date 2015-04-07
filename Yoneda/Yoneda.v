Require Import Category.Main.
Require Import Cat.Facts.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Functor.Representable.Hom_Func.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.

Section Y_emb.
  Context (C : Category).

  Instance CoYoneda : Functor C^op (Func_Cat C Type_Cat) := Exp_Cat_morph_ex (Hom_Func C).
  
  Instance Yoneda : Functor C (Func_Cat C^op Type_Cat) := Exp_Cat_morph_ex (Hom_Func C^op).

End Y_emb.

Section Y_Left_Right.
  Context (C : Category).

  Instance Y_left : Functor (Prod_Cat C^op (Func_Cat C^op Type_Cat)) Type_Cat :=
    Functor_compose (Prod_Functor (Opposite_Functor (Yoneda C)) (Functor_id (Func_Cat C^op Type_Cat))) (Hom_Func _).

  Instance Y_right : Functor (Prod_Cat C^op (Func_Cat C^op Type_Cat)) Type_Cat :=
    Functor_compose (Twist_Func _ _) (Exp_Cat_Eval C^op Type_Cat).

End Y_Left_Right.

Local Obligation Tactic := idtac.

Program Instance Y_left_to_right (C : Category) : NatTrans (Y_left C) (Y_right C) :=
{
  Trans := fun c_F => fun N => ((Trans N (fst c_F))) (id (fst c_F))
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C [c F] [c' F'] [h1 h2].
  extensionality N; cbn.
  cbn in *.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; cbn.
  apply f_equal.
  match goal with
      [|- _ = ?F _a _ _ ?X (?Y ?Z)] =>
      transitivity (((F _a _ _ X) ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; cbn.
  apply f_equal.
  auto.
Qed.

Next Obligation.
Proof.
  symmetry.
  apply Y_left_to_right_obligation_1.
Qed.
  
Local Obligation Tactic := idtac.

Program Instance Y_right_to_left_NT (C : Category) (c : Obj) (F : Functor C^op Type_Cat) (h : F _o c) : NatTrans ((Yoneda _) _o c) F :=
{
  Trans := fun c' => fun g => (F _a _ _ g) h
}.

Next Obligation. (* Trnas_com *)
Proof.
  intros C c F h c1 c2 h'.
  extensionality g; cbn.
  simpl_ids.
  match goal with
      [|- ?F _a _ _ (?X ∘ ?Y) ?Z = _] =>
      transitivity (((F _a _ _ Y) ∘ (F _a _ _ X)) Z); trivial
  end.
  rewrite <- F_compose; trivial.
Qed.

Next Obligation.
Proof.
  symmetry.
  apply Y_right_to_left_NT_obligation_1.
Qed.

Program Instance Y_right_to_left (C : Category) : NatTrans (Y_right C) (Y_left C) :=
{
  Trans := fun c_F => fun h => Y_right_to_left_NT C (fst c_F) (snd c_F) h
}.

Next Obligation. (* Trans_com *)
Proof.
  intros C [c f] [c' f'] [h N].
  simpl in *.
  extensionality g; cbn.
  apply NatTrans_eq_simplify.
  extensionality d; extensionality g'; cbn.
  simpl_ids.
  match goal with
      [|- ?F _a _ _ ?X (?F _a _ _ ?Y ?Z) = _] =>
      transitivity (((F _a _ _ X) ∘ (F _a _ _ Y)) Z); trivial
  end.
  rewrite <- F_compose; cbn.
  match goal with
      [|- ?X (?Y ?Z) = _] =>
      transitivity ((X ∘ Y) Z); trivial
  end.
  rewrite <- Trans_com; cbn; trivial.
Qed.

Next Obligation.
Proof.
  symmetry.
  apply Y_right_to_left_obligation_1.
Qed.

Lemma Yoneda_Lemma (C : Category) : (Y_left C) ≡≡ (Y_right C) ::> (Func_Cat _ _).
Proof.
  apply NatIso with (n := Y_left_to_right C) (n' := Y_right_to_left C);
    intros [c F]; extensionality x; simpl in *.
  {  
    repeat rewrite (F_id F); reflexivity.
  }
  {
    apply NatTrans_eq_simplify.
    extensionality c'; extensionality h.
    cbn in *.
    simpl_ids.
    match goal with
      [|- ?X (?Y ?Z) = _] =>
      transitivity ((X ∘ Y) Z); trivial
    end.
    rewrite <- Trans_com.
    cbn; auto.
  }
Qed.

Lemma Yoneda_Faithful (C : Category) : Faithful_Func (Yoneda C).
Proof.
  intros c c' f f' H.
  cbn in *.
  match type of H with
      ?X = ?Y =>
      assert(H' : Trans X c id= Trans Y c id)
  end.
  rewrite H; trivial.
  cbn in H'.
  simpl_ids in H'.
  trivial.
Qed.

Lemma Yoneda_Full (C : Category) : Full_Func (Yoneda C).
Proof.
  intros c c' N.
  exists (Trans (Y_left_to_right C) (c, (((Yoneda C) _o) c')) N).
  apply NatTrans_eq_simplify.
  extensionality x; extensionality h.
  transitivity ((((Yoneda C) _o c') _a _ _ h ∘ (Trans N c)) id).
  + cbn; auto.
  + rewrite <- Trans_com.
    cbn; auto.
Qed.

Instance Yoneda_Emb (C : Category) : Embedding C (Func_Cat C ^op Type_Cat) :=
{
  Emb_Func := Yoneda C;
  Emb_Faithful := Yoneda_Faithful C;
  Emb_Full := Yoneda_Full C
}.

Theorem Yoneda_Iso (C : Category) : forall (c c' : Obj), (Yoneda C) _o c ≡ (Yoneda C) _o c' → c ≡ c'.
Proof.
  intros.
  apply (Emb_Conservative _ _ (Yoneda_Emb C) _); trivial.
Qed.

Ltac Yoneda := apply Yoneda_Iso.

Theorem CoYoneda_Iso (C : Category) : forall (c c' : Obj), (CoYoneda C) _o c ≡ (CoYoneda C) _o c' → c ≡ c'.
Proof.
  intros; Yoneda; trivial.
Qed.

Ltac CoYoneda := apply CoYoneda_Iso.