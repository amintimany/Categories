Require Import Category.Core.
Require Import Functor.Core.
Require Import Basic_Cons.Initial.

Section CoCones.

  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} {J : Category ObjJ HomJ}
          `{C : Category Obj Hom} (D : Functor J C).
  
  Class CoCone : Type :=
    {
      CoCone_obj : Obj;
  
      CoCone_arrow : ∀ (c : ObjJ), Hom (D _o c) CoCone_obj;

      CoCone_com : ∀ (c d : ObjJ) (h : HomJ c d), (CoCone_arrow d) ∘ (D _a _ _ h) = CoCone_arrow c
    }.

  Coercion CoCone_obj : CoCone >-> Obj.

  Class CoCone_Morph (c c' : CoCone) : Type :=
    {
      CoCone_Morph_arrow : Hom c c';

      CoCone_Morph_com : ∀ (a : ObjJ),  CoCone_Morph_arrow ∘ (@CoCone_arrow c a) = (@CoCone_arrow c' a)
    }.

  Coercion CoCone_Morph_arrow : CoCone_Morph >-> Hom.

  Lemma CoCone_Morph_eq_simplify (c c' : CoCone) (h h': CoCone_Morph c c') :
    (@CoCone_Morph_arrow _ _ h) = (@CoCone_Morph_arrow _ _ h') -> h = h'.
  Proof.
    intros H.
    destruct h as [ha hc]; destruct h' as [ha' hc']; simpl in *.
    destruct H.
    destruct (proof_irrelevance _ hc hc').
    reflexivity.
  Qed.

  Hint Extern 1 (?A = ?B :> CoCone_Morph _ _) => apply CoCone_Morph_eq_simplify; simpl.

  Program Instance Cone_Morph_id (c : CoCone) : CoCone_Morph c c :=
    {
      CoCone_Morph_arrow := id
    }.
  
  (* Cone_Morph_id defined *)


  Program Instance Cone_Morph_compose (c c' c'' : CoCone) (h : CoCone_Morph c c') (h' : CoCone_Morph c' c'') : CoCone_Morph c c'' :=
    {
      CoCone_Morph_arrow := h' ∘ h
    }.

  Next Obligation. (* CoCone_Morph_arrow *)
  Proof.
    rewrite assoc.
    repeat rewrite CoCone_Morph_com.
    trivial.
  Qed.

  (* Cone_Morph_compose defined *)

  Program Instance CoCone_Cat : Category CoCone CoCone_Morph :=
    {
      compose := Cone_Morph_compose;
      id := Cone_Morph_id
    }.

  (* Cone_Cat defined *)

End CoCones.

Arguments CoCone_obj {_ _ _ _ _ _ _} _.
Arguments CoCone_arrow {_ _ _ _ _ _ _} _ _.
Arguments CoCone_com {_ _ _ _ _ _ _} _ {_ _} _.

Arguments CoCone_Morph_arrow {_ _ _ _ _ _ _ _ _} _.
Arguments CoCone_Morph_com {_ _ _ _ _ _ _ _ _} _ _.

Hint Extern 1 (?A = ?B :> CoCone_Morph _ _ _) => apply CoCone_Morph_eq_simplify; simpl.

Notation CoLimit D c := (Initial (CoCone_Cat D) c).

Notation Has_CoLimit D := (Has_Initial (CoCone_Cat D)).

Notation CoComplete C := (∀ `{J : Category Obj' Hom'} (D : Functor J C), Has_CoLimit D).







