Require Import Category.Main.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Section NatTrans.
  Context {C C' : Category}.

  Class NatTrans (F F' : Functor C C') :=
    {
      Trans (c : C) : Hom (F _o c) (F' _o c);
      Trans_com {c c' : C} (h : Hom c c') : (Trans c') ∘ F _a _ _ h = F' _a _ _ h ∘ (Trans c)
    }.

  Arguments Trans {_ _} _ _.

  (* NatTrans_Setoid defined *)

  Lemma NatTrans_eq_simplify {F F' : Functor C C'} (N N' : NatTrans F F') : (@Trans _ _ N) = (@Trans _ _ N') -> N = N'.
  Proof.
    intros H1.
    destruct N as [NT NC]; destruct N' as [NT' NC']; simpl in *.
    destruct H1.
    destruct (proof_irrelevance _ NC NC').
    trivial.
  Qed.

  Program Instance NatTrans_compose {F F' F'' : Functor C C'} (tr : NatTrans F F') (tr' : NatTrans F' F'') : NatTrans F F'' :=
    {
      Trans := fun c : Obj => (Trans tr' c) ∘ (Trans tr c)
    }.

  Next Obligation. (* Trans_com*)
  Proof.
    rewrite assoc.
    rewrite Trans_com.
    match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
    rewrite Trans_com; auto.
  Qed.

  (* NatTrans_compose defined *)

  Program Instance NatTrans_id {F : Functor C C'} : NatTrans F F :=
    {
      Trans := fun x : Obj => F _a _ _ id
    }.

  (* NatTrans_id defined *)

End NatTrans.

Arguments Trans {_ _} [_ _] _ _.

Hint Resolve NatTrans_eq_simplify.

Local Hint Extern 1 => apply NatTrans_eq_simplify; simpl.

Program Instance Func_Cat (C C' : Category) : Category :=
{
  Obj := Functor C C';

  Hom := NatTrans;

  compose := @NatTrans_compose _ _;

  id := @NatTrans_id _ _
}.

Section NatIso.
  Context {C C' : Category} (F G : Functor C C') (n : NatTrans F G) (n' : NatTrans G F).

  Theorem NatIso : (∀ (c : Obj), (Trans n c) ∘ (Trans n' c) = G _a _ _ (@id _ c)) →
                   (∀ (c : Obj), (Trans n' c) ∘ (Trans n c) = F _a _ _ (@id _ c)) →
                   F ≡≡ G ::> Func_Cat _ _.
  Proof.
    intros H1 H2.
    apply (@Build_Isomorphism (Func_Cat _ _) _ _ n n'); auto.
  Qed.

End NatIso.














