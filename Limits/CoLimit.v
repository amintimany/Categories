Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Initial.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Set Primitive Projections.

Set Universe Polymorphism.

Section CoLimit.

  Context {J C : Category} (D : Functor J C).
  
  Class CoCone : Type :=
    {
      CoCone_obj : @Obj C;
  
      CoCone_arrow : ∀ (c : @Obj J), Hom (D _o c) CoCone_obj;

      CoCone_com : ∀ (c d : @Obj J) (h : @Hom J c d), (CoCone_arrow d) ∘ (D _a _ _ h) = CoCone_arrow c
    }.

  Coercion CoCone_obj : CoCone >-> Obj.

  Class CoCone_Morph (c c' : CoCone) : Type :=
    {
      CoCone_Morph_arrow : Hom c c';

      CoCone_Morph_com : ∀ (a : Obj),  CoCone_Morph_arrow ∘ (@CoCone_arrow c a) = (@CoCone_arrow c' a)
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

  Program Instance CoCone_Cat : Category :=
    {
      Obj := CoCone;
      Hom := CoCone_Morph;
      compose := Cone_Morph_compose;
      id := Cone_Morph_id
    }.

  Existing Instance CoCone_Cat.

  (* Cone_Cat defined *)

  Class CoLimit (l : CoCone) : Type := CoLim_init : Initial CoCone_Cat l.
  
End CoLimit.

Arguments CoCone_obj {_ _ _} _.
Arguments CoCone_arrow {_ _ _} _ _.
Arguments CoCone_com {_ _ _} _ {_ _} _.

Arguments CoCone_Morph_arrow {_ _ _ _ _} _.
Arguments CoCone_Morph_com {_ _ _ _ _} _ _.

Hint Extern 1 (?A = ?B :> CoCone_Morph _ _ _) => apply CoCone_Morph_eq_simplify; simpl.

Class Has_CoLimit {C J : Category} (D : Functor J C) :=
{
  HCL_CoLimit : CoCone D;

  HCL_CoLimit_CoLimit : CoLimit D HCL_CoLimit
}.

Existing Instance HCL_CoLimit_CoLimit.


Class Has_Restricted_CoLimits (C : Category) (P : Card_Restriction) :=
{
  Restricted_CoLimit_of {J : Category} (D : Functor J C) : (P (@Obj J)) → (P (Arrow J)) → CoCone D;
  Restricted_CoLimit_of_CoLimit {J : Category} (D : Functor J C) (PO : P (@Obj J)) (PH : P (Arrow J)) : CoLimit D (Restricted_CoLimit_of D PO PH)
}.

Existing Instance Restricted_CoLimit_of_CoLimit.

Class CoComplete (C : Category) :=
{
  CoLimit_of {J : Category} (D : Functor J C) : CoCone D;
  CoLimit_of_CoLimit {J : Category} (D : Functor J C) : CoLimit D (CoLimit_of D)
}.

Existing Instance CoLimit_of_CoLimit.


Section Restricted_CoLimits_to_CoComplete.
  Context (C : Category) (P : Card_Restriction) {HRL : Has_Restricted_CoLimits C P} (All_Ps : ∀ t, P t).
  
  Instance No_Restriction_CoComplete : CoComplete C :=
    {
      CoLimit_of := λ J D, Restricted_CoLimit_of D (All_Ps (@Obj J)) (All_Ps (Arrow J))
    }.

End Restricted_CoLimits_to_CoComplete.

Section CoComplete_to_Restricted_CoLimits.
  Context (C : Category) {CC : CoComplete C} (P : Card_Restriction).
  
  Instance CoComplete_Has_Restricted_CoLimits : Has_Restricted_CoLimits C P :=
    {
      Restricted_CoLimit_of := λ J D _ _, CoLimit_of D
    }.

End CoComplete_to_Restricted_CoLimits.


