Require Import Category.Main.
Require Import Functor.Main.

Section NatTrans.
  Context {C C' : Category}.

  Class NatTrans (F F' : Functor C C') :=
    {
      Trans (c : C) : Hom (F _o c) (F' _o c);
      Trans_com {c c' : C} (h : Hom c c') : (Trans c') ∘ F _a _ _ h = F' _a _ _ h ∘ (Trans c);
      Trans_com_sym {c c' : C} (h : Hom c c') : F' _a _ _ h ∘ (Trans c) = (Trans c') ∘ F _a _ _ h
    }.

  Arguments Trans {_ _} _ _.

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
    rewrite assoc.
    rewrite Trans_com.
    match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
    rewrite Trans_com; auto.
  Qed.
  
  (* NatTrans_compose defined *)

  Program Instance NatTrans_id (F : Functor C C') : NatTrans F F :=
    {
      Trans := fun x : Obj => F _a _ _ id
    }.

  (* NatTrans_id defined *)

End NatTrans.

Arguments Trans {_ _ _ _} _ _.
Arguments Trans_com {_ _ _ _} _ {_ _} _.

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
    apply (Build_Isomorphism (Func_Cat _ _) _ _ n n'); auto.
  Qed.

End NatIso.

Section Opposite_NatTrans.
  Context {C D : Category} {F F' : Functor C D} (N : NatTrans F F').

  Instance Opposite_NatTrans : NatTrans (Opposite_Functor F') (Opposite_Functor F) :=
    {
      Trans := Trans N;
      Trans_com := fun c c' h => (@Trans_com_sym _ _ _ _ N _ _ h);
      Trans_com_sym := fun c c' h => (@Trans_com _ _ _ _ N _ _ h)
    }.
  
End Opposite_NatTrans.
  
(* Horizontal composition of natural transformations *)

Program Instance NatTrans_hor_comp {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (tr : NatTrans F G) (tr' : NatTrans F' G') : NatTrans (Functor_compose F F') (Functor_compose G G') :=
{
  Trans := fun c : Obj => (G' _a _ _ (Trans tr c)) ∘ (Trans tr' (F _o c))
}.

Next Obligation. (* Trans_com*)
Proof.
  rewrite assoc.
  rewrite Trans_com.
  match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
  rewrite <- F_compose.
  rewrite Trans_com.
  rewrite F_compose.
  auto.
Qed.

Next Obligation. (* Trans_com*)
Proof.
  symmetry.
  rewrite assoc.
  rewrite Trans_com.
  match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
  rewrite <- F_compose.
  rewrite Trans_com.
  rewrite F_compose.
  auto.
Qed.

Program Instance NatTrans_to_compose_id {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose F (Functor_id _)) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_compose_id {C D : Category} (F : Functor C D) : NatTrans (Functor_compose F (Functor_id _)) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_to_id_compose {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose (Functor_id _) F) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_id_compose {C D : Category} (F : Functor C D) : NatTrans (Functor_compose (Functor_id _) F) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose F (Functor_compose G H)) (Functor_compose (Functor_compose F G) H) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc_sym {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose (Functor_compose F G) H) (Functor_compose F (Functor_compose G H)) :=
{
  Trans := fun c => id
}.