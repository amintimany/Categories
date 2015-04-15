Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.

Section NatTrans.
  Context {C C' : Category}.

  Class NatTrans (F F' : Functor C C') :=
    {
      Trans (c : C) : Hom (F _o c) (F' _o c);
      Trans_com {c c' : C} (h : Hom c c') : (Trans c') ∘ F _a _ _ h = F' _a _ _ h ∘ (Trans c);
      Trans_com_sym {c c' : C} (h : Hom c c') : F' _a _ _ h ∘ (Trans c) = (Trans c') ∘ F _a _ _ h
    }.

  Arguments Trans {_ _} _ _.
  Arguments Trans_com {_ _ _ _} _ _.
  Arguments Trans_com_sym {_ _ _ _} _ _.

  
  (* NatTrans_Setoid defined *)

  Lemma NatTrans_eq_simplify {F F' : Functor C C'} (N N' : NatTrans F F') : (@Trans _ _ N) = (@Trans _ _ N') -> N = N'.
  Proof.
    intros H1.
    destruct N as [NT NC NCs]; destruct N' as [NT' NC' NCs']; cbn in *.
    destruct H1.
    destruct (proof_irrelevance _ NC NC').
    destruct (proof_irrelevance _ NCs NCs').    
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

  Next Obligation. (* Trans_com_sym *)
  Proof.
    symmetry.
    apply NatTrans_compose_obligation_1.
  Qed.

  (* NatTrans_compose defined *)

  Theorem NatTrans_compose_assoc {F G H I : Functor C C'} (N : NatTrans F G) (N' : NatTrans G H) (N'' : NatTrans H I) : NatTrans_compose N (NatTrans_compose N' N'') = NatTrans_compose (NatTrans_compose N N') N''.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn; auto.
  Qed.
    
  Program Instance NatTrans_id (F : Functor C C') : NatTrans F F :=
    {
      Trans := fun x : Obj => id
    }.

  (* NatTrans_id defined *)

  Theorem NatTrans_id_unit_left {F G : Functor C C'} (N : NatTrans F G) : NatTrans_compose N (NatTrans_id G) = N.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn; auto.
  Qed.

  Theorem NatTrans_id_unit_right {F G : Functor C C'} (N : NatTrans F G) : NatTrans_compose (NatTrans_id F) N = N.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn; auto.
  Qed.
  
End NatTrans.

Arguments Trans {_ _ _ _} _ _.
Arguments Trans_com {_ _ _ _} _ {_ _} _.
Arguments Trans_com_sym {_ _ _ _} _ {_ _} _.

Hint Resolve NatTrans_eq_simplify.
