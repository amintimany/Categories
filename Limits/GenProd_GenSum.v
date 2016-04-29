Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Archetypal.Discr.Discr Archetypal.Discr.NatFacts.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Cat.Cat_Iso.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import KanExt.LocalFacts.NatIso.

Require Import Limits.Limit.
Require Import Limits.Isomorphic_Cat.

Section GenProd_Sum.
  Context {A : Type} {C : Category} (map : A → C).

  Definition GenProd := Limit (Discr_Func map).

  Identity Coercion GenProd_Limit : GenProd >-> Limit.
  
  Definition GenSum := CoLimit (Discr_Func_op map).

  Identity Coercion GenSum_CoLimit : GenSum >-> CoLimit.

End GenProd_Sum.

Arguments GenProd {_}%type {_}%category _, {_} _ _.
Arguments GenSum {_}%type {_}%category _, {_} _ _.

Notation "'Π' m" := (GenProd m) : object_scope.

Notation "'Σ' m" := (GenSum m) : object_scope.

Notation "'Π_' C ↓ m" := (GenProd C m) : object_scope.

Notation "'Σ_' C ↓ m" := (GenSum C m) : object_scope.

(** The fact That if a category has generalized products of some type,
    its dual also has generalized sums of that type. *)

Section GenProd_to_GenSum.
  Context {A : Type} {C : Category} {map : A → C} (L : (Π map)%object).
  
  Definition GenProd_to_GenSum : (Σ_ (C^op) ↓ map)%object :=
    Local_Right_KanExt_Iso ((@Discr_Func_Iso (C^op) A map)⁻¹) L.

End GenProd_to_GenSum.

(** The fact That if a category has generalized sums of some type, its dual has
generalized products of that type. *)
Section GenSum_to_GenProd.
  Context {A : Type} {C : Category} {map : A → C} (L : (Σ map)%object).
  
  Definition GenSum_to_GenProd : (Π_ (C^op) ↓ map)%object :=
    Local_Right_KanExt_Iso (Discr_Func_Iso map) L.

End GenSum_to_GenProd.

(** If we have GenSum for all functions from a type A, where A is isomorphic
to B we have all GenSum for all functions from B. We show this by showing
that for the underlying functor of any GenSum from B is isomorphic to the
underlying functor of some GenSum from A pre-composed with the provided
isomorphism.
*)
Section GenSum_IsoType.
  Context {A B : Type} (Iso : (A ≃≃ B ::> Type_Cat)%isomorphism) {C : Category}
          (SM : forall f : A → C, (Σ f)%object).

  Program Definition GenSum_IsoType_map_Iso (map : B → C):
    (
      ((((Discr_Func_op map)^op)%functor)
         ≃≃ ((Discr_Func_op
                (fun x : A => map ((iso_morphism Iso) x))
                ∘ (iso_morphism (Opposite_Cat_Iso
                                   (Inverse_Isomorphism
                                      (Discr_Cat_Iso Iso)))))^op
            )%functor
        ::> Func_Cat _ _)%isomorphism
    )%morphism
    :=
      {|
        iso_morphism :=
          {|
            Trans :=
              Trans
                (iso_morphism
                   (IsoCat_NatIso (Opposite_Cat_Iso
                                     (Discr_Cat_Iso Iso)) (Discr_Func_op map))
                )
          |};
        inverse_morphism :=
          {|
            Trans :=
              Trans
                (inverse_morphism
                   (IsoCat_NatIso (Opposite_Cat_Iso
                                     (Discr_Cat_Iso Iso)) (Discr_Func_op map))
                )
          |}
      |}
  .

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    apply (
        f_equal
          Trans
          (
            right_inverse
              (IsoCat_NatIso (Opposite_Cat_Iso
                                (Discr_Cat_Iso Iso)) (Discr_Func_op map))
          )
      ).
  Qed.
  
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    apply (
        f_equal
          Trans
          (
            left_inverse
              (IsoCat_NatIso (Opposite_Cat_Iso
                                (Discr_Cat_Iso Iso)) (Discr_Func_op map))
          )
      ).
  Qed.
  
  Definition  GenSum_IsoType (map : B → C) : (Σ map)%object :=
    Local_Right_KanExt_Iso
      (GenSum_IsoType_map_Iso map)
      (
        CoLimit_From_Isomorphic_Cat
          (Opposite_Cat_Iso (Inverse_Isomorphism (Discr_Cat_Iso Iso)))
          (SM (fun x : A => map ((iso_morphism Iso) x)))
      ).

End GenSum_IsoType.