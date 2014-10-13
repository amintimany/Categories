Require Import Category.Core.
Require Import Functor.Core.
Require Import Basic_Cons.Terminal.

Section Cones.

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

  (* Cone_Cat defined *)

End Cones.

Arguments Cone_obj {_ _ _ _ _ _ _} _.
Arguments Cone_arrow {_ _ _ _ _ _ _} _ _.
Arguments Cone_com {_ _ _ _ _ _ _} _ {_ _} _.

Arguments Cone_Morph_arrow {_ _ _ _ _ _ _ _ _} _.
Arguments Cone_Morph_com {_ _ _ _ _ _ _ _ _} _ _.

Hint Extern 1 (?A = ?B :> Cone_Morph _ _ _) => apply Cone_Morph_eq_simplify; simpl.

Notation Limit D c := (Terminal (Cone_Cat D) c).

Notation Has_Limit D := (Has_Terminal (Cone_Cat D)).

Notation Complete C := (∀ `{J : Category Obj' Hom'} (D : Functor J C), Has_Limit D).








