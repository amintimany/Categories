Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Terminal.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Section Limit.

  Context `{J : Category Obj' Hom'}
          `{C : Category Obj Hom} (D : Functor J C).
  
  Class Cone : Type :=
    {
      Cone_obj : Obj;
  
      Cone_arrow : ∀ (c : Obj'), Hom Cone_obj (D _o c);

      Cone_com : ∀ (c d : Obj') (h : Hom' c d), (D _a _ _ h) ∘ (Cone_arrow c) = Cone_arrow d
    }.

  Coercion Cone_obj : Cone >-> Obj.

  Class Cone_Morph (c c' : Cone) : Type :=
    {
      Cone_Morph_arrow : Hom c c';

      Cone_Morph_com : ∀ (a : Obj'),  (@Cone_arrow c' a) ∘ Cone_Morph_arrow = (@Cone_arrow c a)
    }.

  Coercion Cone_Morph_arrow : Cone_Morph >-> Hom.

  Lemma Cone_Morph_eq_simplify (c c' : Cone) (h h': Cone_Morph c c') :
    (@Cone_Morph_arrow _ _ h) = (@Cone_Morph_arrow _ _ h') -> h = h'.
  Proof.
    intros H.
    destruct h as [ha hc]; destruct h' as [ha' hc']; simpl in *.
    destruct H.
    destruct (proof_irrelevance _ hc hc').
    reflexivity.
  Qed.

  Hint Extern 1 (?A = ?B :> Cone_Morph _ _) => apply Cone_Morph_eq_simplify; simpl.

  Program Instance Cone_Morph_id (c : Cone) : Cone_Morph c c :=
    {
      Cone_Morph_arrow := id
    }.
  
  (* Cone_Morph_id defined *)


  Program Instance Cone_Morph_compose (c c' c'' : Cone) (h : Cone_Morph c c') (h' : Cone_Morph c' c'') : Cone_Morph c c'' :=
    {
      Cone_Morph_arrow := h' ∘ h
    }.

  Next Obligation. (* Cone_Morph_arrow *)
  Proof.
    rewrite <- assoc.
    repeat rewrite Cone_Morph_com.
    trivial.
  Qed.

  (* Cone_Morph_compose defined *)

  Program Instance Cone_Cat : Category Cone Cone_Morph :=
    {
      compose := Cone_Morph_compose;
      id := Cone_Morph_id
    }.

  Existing Instance Cone_Cat.

  (* Cone_Cat defined *)

  Class Limit (l : Cone) : Type := Lim_term : Terminal Cone_Cat l.

End Limit.

Arguments Cone_obj {_ _ _ _ _ _ _} _.
Arguments Cone_arrow {_ _ _ _ _ _ _} _ _.
Arguments Cone_com {_ _ _ _ _ _ _} _ {_ _} _.

Arguments Cone_Morph_arrow {_ _ _ _ _ _ _ _ _} _.
Arguments Cone_Morph_com {_ _ _ _ _ _ _ _ _} _ _.

Hint Extern 1 (?A = ?B :> Cone_Morph _ _ _) => apply Cone_Morph_eq_simplify; simpl.

Class Has_Limit `{C : Category Obj Hom} `{J : Category Obj' Hom'} (D : Functor J C) :=
{
  HL_Lim : Cone D;

  HL_Lim_Limit : Limit D HL_Lim
}.

Existing Instance HL_Lim_Limit.

Class Has_Restricted_Limits `(C : Category Obj Hom) (P : Card_Restriction) :=
{
  Restricted_Limit_of `{J : Category Obj' Hom'} (D : Functor J C) : (P Obj') → (P (Arrow J)) → Cone D;

  Restricted_Limit_of_Limit `{J : Category Obj' Hom'} (D : Functor J C) (PO : P Obj') (PH : P (Arrow J)) : Limit D (Restricted_Limit_of D PO PH)
}.

Existing Instance Restricted_Limit_of_Limit.

Class Complete `(C : Category Obj Hom) :=
{
  Limit_of `{J : Category Obj' Hom'} (D : Functor J C) : Cone D;

  Limit_of_Limit `{J : Category Obj' Hom'} (D : Functor J C) : Limit D (Limit_of D)
}.

Existing Instance Limit_of_Limit.

Section Restricted_Limits_to_Complete.
  Context `(C : Category Obj Hom) (P : Card_Restriction) {HRL : Has_Restricted_Limits C P} (All_Ps : ∀ t, P t).
  
  Instance No_Restriction_Complete : Complete C :=
    {
      Limit_of := λ O H J D, Restricted_Limit_of D (All_Ps O) (All_Ps (Arrow J))
    }.

End Restricted_Limits_to_Complete.

Section Complete_to_Restricted_Limits.
  Context `(C : Category Obj Hom) {CC : Complete C} (P : Card_Restriction).
  
  Instance Complete_Has_Restricted_Limits : Has_Restricted_Limits C P :=
    {
      Restricted_Limit_of := λ _ _ J D _ _, Limit_of D
    }.

End Complete_to_Restricted_Limits.
