Require Import Category.Main.

Class Functor (C C' : Category) : Type := 
{
  (* Object map *)
  FO : C → C';

  (* Arrow map *)
  FA : ∀ {a b}, Hom C a b → Hom C' (FO a) (FO b);

  (* Mapping of identities *)
  F_id : ∀ c, FA (id c) = id (FO c);
  
  (* Functor commuting with composition *)
  F_compose : ∀ {a b c} (f : Hom a b) (g : Hom b c), FA (g ∘ f) = (FA g) ∘ (FA f)

  (* F_id and F_compose together state the fact that functors are morphisms of categories (preserving the structure of categories!)*)
}.

Arguments FO {_ _} _ _.
Arguments FA {_ _} _ {_ _} _, {_ _} _ _ _ _.
Arguments F_id {_ _} _ _.
Arguments F_compose {_ _} _ {_ _ _} _ _.

Notation "F '_o'" := (FO F) : object_scope.

Notation "F '_a'" := (@FA _ _ F) : morphism_scope.

Hint Extern 2 => (apply F_id).

Ltac Functor_Simplify :=
  match goal with
    | [|- ?F _a _ _ ?A = id (?F _o ?x)] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- (id (?F _o ?x)) = ?F _a _ _ ?A] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C ∘ ?F _a _ _ ?D] =>
      repeat rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?C = ?F _a _ _ ?A ∘ ?F _a _ _ ?B] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- context [?F _a _ _ id] ] =>
      rewrite F_id; (simpl||idtac)
    | [|- context [?F _a _ _ ?A ∘ ?F _a _ _ ?B]] =>
      rewrite <- F_compose; (simpl||idtac)
  end
.

Hint Extern 2 => Functor_Simplify.

Section Functor_eq_simplification.

  Context {C C' : Category} (F G : Functor C C').

  Lemma Functor_eq_simplify (Oeq : F _o = G _o) :
    ((fun x y => match Oeq in _ = V return Hom x y → Hom C' (V x) (V y) with eq_refl => F  _a x y end) = G _a) -> F = G.
  Proof.
    intros H.
    destruct F as [fO fA fid fco]; destruct G as [gO gA gid gco]; cbn in *.
    destruct Oeq.
    destruct H.
    destruct (proof_irrelevance _ fid gid).
    destruct (proof_irrelevance _ fco gco).
    reflexivity.
  Qed.

  Theorem FA_extensionality (Oeq : F _o = G _o) : (∀ (a b : Obj) (h : Hom a b), (fun x y => match Oeq in _ = V return Hom x y → Hom C' (V x) (V y) with eq_refl => F  _a x y end) _ _ h = G _a _ _ h) → (fun x y => match Oeq in _ = V return Hom x y → Hom C' (V x) (V y) with eq_refl => F  _a x y end) = G _a.
  Proof.
    intros H.
    extensionality x; extensionality y; extensionality h; apply H.
  Qed.

  Lemma Functor_extensionality (Oeq : F _o = G _o) : (∀ (a b : Obj) (h : Hom a b), (fun x y => match Oeq in _ = V return Hom x y → Hom C' (V x) (V y) with eq_refl => F  _a x y end) _ _ h = G _a _ _ h) → F = G.
  Proof.
    intros H.
    apply (Functor_eq_simplify Oeq); trivial.
    apply FA_extensionality; trivial.
  Qed.

End Functor_eq_simplification.

Hint Extern 2 => Functor_Simplify.
