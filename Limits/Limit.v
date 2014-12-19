Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Terminal.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Set Primitive Projections.

Set Universe Polymorphism.

Section Limit.

  Context {J C : Category} (D : Functor J C).
  
  Class Cone : Type :=
    {
      cone : C;
  
      Cone_arrow : ∀ (c : J), Hom cone (D _o c);

      Cone_com : ∀ (c d : J) (h : Hom c d), (D _a _ _ h) ∘ (Cone_arrow c) = Cone_arrow d
    }.

  Coercion cone : Cone >-> Obj.

  Class Cone_Hom (c c' : Cone) : Type :=
    {
      cone_hom : Hom c c';

      Cone_Hom_com : ∀ (a : J),  (@Cone_arrow c' a) ∘ cone_hom = (@Cone_arrow c a)
    }.

  Coercion cone_hom : Cone_Hom >-> Hom.

  Lemma Cone_Morph_eq_simplify (c c' : Cone) (h h': Cone_Hom c c') :
    h = h' :> Hom _ _ -> h = h'.
  Proof.
    intros H.
    destruct h as [ha hc]; destruct h' as [ha' hc']; simpl in *.
    destruct H.
    destruct (proof_irrelevance _ hc hc').
    reflexivity.
  Qed.

  Hint Extern 1 (?A = ?B :> Cone_Hom _ _) => apply Cone_Morph_eq_simplify; simpl.

  Program Instance Cone_Hom_id (c : Cone) : Cone_Hom c c :=
    {
      cone_hom := id
    }.
  
  (* Cone_Morph_id defined *)


  Program Instance Cone_Hom_compose (c c' c'' : Cone) (h : Cone_Hom c c') (h' : Cone_Hom c' c'') : Cone_Hom c c'' :=
    {
      cone_hom := h' ∘ h
    }.

  Next Obligation. (* Cone_Morph_arrow *)
  Proof.
    rewrite <- assoc.
    repeat rewrite Cone_Hom_com; trivial.
  Qed.

  (* Cone_Morph_compose defined *)

  Program Instance Cone_Cat : Category :=
    {
      Obj := Cone;
      Hom := Cone_Hom;
      compose := Cone_Hom_compose;
      id := Cone_Hom_id
    }.

  (* Cone_Cat defined *)

  Class Limit : Type := limit : Terminal Cone_Cat.

  (* Estabilishing new path in coercion graph to take limits directly to objects of the underlying category (C) instead of objects of Cone_Cat *)

  Definition limit_to_obj (l : Limit) : C.
  Proof.
    apply l.
  Defined.

  Coercion limit_to_obj : Limit >-> Obj.

End Limit.

Theorem Limit_Cone_Cat_Iso {J C : Category} {D : Functor J C} (l l' : Limit D) : (@limit _ _ _ l) ≡≡ (@limit _ _ _ l') ::> Cone_Cat _.
  apply (@Build_Isomorphism _ _ _ (@t_morph _ l' (@limit _ _ _ l)) (@t_morph _ l (@limit _ _ _ l'))); apply t_morph_unique.
Qed.

Theorem Limit_Iso {J C : Category} {D : Functor J C} (l l' : Limit D) : l ≡≡ l' ::> C.
  apply (@Build_Isomorphism C _ _ (@iso_morphism _ _ _ (Limit_Cone_Cat_Iso l l')) (@inverse_morphism _ _ _ (Limit_Cone_Cat_Iso l l'))).
  apply (f_equal (@cone_hom _ _ _ _ _) (@left_inverse _ _ _ (Limit_Cone_Cat_Iso l l'))).
  apply (f_equal (@cone_hom _ _ _ _ _) (@right_inverse _ _ _ (Limit_Cone_Cat_Iso l l'))).
Qed.

Arguments cone {_ _ _} _.
Arguments Cone_arrow {_ _ _} _ _.
Arguments Cone_com {_ _ _} _ {_ _} _.

Arguments cone_hom {_ _ _ _ _} _.
Arguments Cone_Hom_com {_ _ _ _ _} _ _.

Hint Extern 1 (?A = ?B :> Cone_Hom _ _ _) => apply Cone_Morph_eq_simplify; simpl.

Class Has_Restr_Limits (C : Category) (P : Card_Restriction) := has_restr_limits : ∀ {J : Category} (D : Functor J C), P J → P (Arrow J) → Limit D.

Class Complete (C : Category) := complete : ∀ {J : Category} (D : Functor J C), Limit D.

Section Restricted_Limits_to_Complete.
  Context (C : Category) (P : Card_Restriction) {HRL : Has_Restr_Limits C P} (All_Ps : ∀ t, P t).
  
  Instance No_Restriction_Complete : Complete C :=
    {
      complete := λ J D, HRL _ D (All_Ps J) (All_Ps (Arrow J))
    }.

End Restricted_Limits_to_Complete.

Section Complete_to_Restricted_Limits.
  Context (C : Category) {CC : Complete C} (P : Card_Restriction).
  
  Instance Complete_Has_Restricted_Limits : Has_Restr_Limits C P :=
    {
      has_restr_limits := λ J D _ _, CC _ D
    }.

End Complete_to_Restricted_Limits.

Notation CoCone F := (Cone (Opposite_Functor F)) (only parsing).

Notation CoCone_Hom F := (Cone_Hom (Opposite_Functor F)) (only parsing).

Notation CoLimit F := (Limit (Opposite_Functor F)) (only parsing).

Notation CoComplete C := (Complete C^op) (only parsing).

Notation Has_Restr_CoLimits C P := (Has_Restr_Limits C^op P) (only parsing).