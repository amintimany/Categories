(**
    This file contains the basic definitions for Isomorphisms Monomorphisms, Epimorphisms and when two objects are isomorphic.

*)

Require Import Category.Category.
Require Import Category.Tactics.

Class Isomorphism `{C : Category Obj Hom} {a b : Obj} (f : Hom a b) : Type := 
{
  inverse_morphism : Hom b a;
  
  left_inverse : inverse_morphism ∘ f = id;
  
  right_inverse : f ∘ inverse_morphism = id
}.

Arguments inverse_morphism {_ _ _ _ _} _ {_}.

Notation "f '⁻¹'" := (inverse_morphism f) (at level 7, no associativity).

Instance Inverse_Isomorphism `{C : Category Obj Hom} {a b : Obj} {f : Hom a b} (I : Isomorphism f) : Isomorphism (inverse_morphism f) :=
{
  inverse_morphism := f;
  left_inverse := right_inverse;
  right_inverse := left_inverse
}.

Program Instance Isomorphism_Compose `{C : Category Obj Hom} {a b c : Obj} {f : Hom a b} {g : Hom b c} (I : Isomorphism f) (I' : Isomorphism g): Isomorphism (g ∘ f) :=
{
  inverse_morphism := (inverse_morphism f ∘ inverse_morphism g)
}.

Next Obligation. (* left_inverse *)
Proof.
  match goal with
      [|- (?A ∘ ?B) ∘ ?C ∘ _ = _] =>
      reveal_comp B C
  end.
  rewrite left_inverse; simpl_ids.
  apply left_inverse.
Qed.

Next Obligation. (* right_inverse *)
Proof.
  match goal with
      [|- (?A ∘ ?B) ∘ ?C ∘ _ = _] =>
      reveal_comp B C
  end.
  rewrite right_inverse; simpl_ids.
  apply right_inverse.
Qed.

Class Isomorphic `{C : Category Obj Hom} (a b : Obj) :=
{
  iso_morphism : Hom a b;
  
  iso_morphism_isomorphism : Isomorphism iso_morphism
}.

Existing Instance iso_morphism_isomorphism.

Definition iso_morphism_HOM `{C : Category Obj Hom} {a b : Obj} (I : Isomorphic a b) : HOM a b :=
  @iso_morphism _ _ _ _ _ I.

Coercion iso_morphism_HOM : Isomorphic >-> HOM.

Coercion iso_morphism_isomorphism : Isomorphic >-> Isomorphism.

Notation "a ≡ b" := (Isomorphic a b) (at level 70, no associativity).

Section Isomorphic_equiv.
    Context `{C : Category Obj Hom} (a b c : Obj).
    
    Theorem Isomorphic_refl : a ≡ a.
    Proof.
      do 2 exists id; auto.
    Qed.

    Theorem Isomorphic_sym : a ≡ b → b ≡ a.
    Proof.
      intros I.
      eapply (Build_Isomorphic _ _ _ _ _ _ (Inverse_Isomorphism I)).
    Qed.

    Theorem Isomorphic_trans : a ≡ b → b ≡ c → a ≡ c.
    Proof.
      intros I I'.
      eapply (Build_Isomorphic _ _ _ _ _ _ (Isomorphism_Compose I I')).
    Qed.

    Hint Resolve Isomorphic_refl Isomorphic_trans.
    Hint Immediate Isomorphic_sym.
  End Isomorphic_equiv.


Class Monic `{C : Category Obj Hom} (a b : Obj) :=
{
  mono_morphism : Hom a b;
  mono_morphism_monomorphism : ∀ (c : Obj) (g h : Hom c a), mono_morphism ∘ g = mono_morphism ∘ h → g = h
}.

Definition mono_morphism_HOM `{C : Category Obj Hom} {a b : Obj} (I : Monic a b) : HOM a b :=
  @mono_morphism _ _ _ _ _ I.

Coercion mono_morphism_HOM : Monic >-> HOM.

Class Epic `{C : Category Obj Hom} (a b : Obj) :=
{
  epi_morphism : Hom a b;
  epi_morphism_epimorphism : ∀ (c : Obj) (g h : Hom b c), g ∘ epi_morphism = h ∘ epi_morphism -> g = h
}.

Definition epi_morphism_HOM `{C : Category Obj Hom} {a b : Obj} (I : Epic a b) : HOM a b :=
  @epi_morphism _ _ _ _ _ I.

Coercion epi_morphism_HOM : Epic >-> HOM.

Notation "a ≫–> b" := (Monic a b).

Notation "a –≫ b" := (Epic a b).

Section Iso_Mono_Epi.

  Context `{C : Category Obj Hom} {a b : Obj} (f : Hom a b) (I : Isomorphism f).

  Program Instance Ismorphism_Monic : a ≫–> b :=
    {
      mono_morphism := f
    }.
  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    cut ((f⁻¹ ∘ f) ∘ g = (f⁻¹ ∘ f) ∘ h).
    {
      intros H'.
      rewrite left_inverse in H'; simpl_ids in H'; trivial.
    }
    {
      repeat rewrite assoc.
      rewrite H.
      reflexivity.
    }
  Qed.

  Program Instance Ismorphism_Epic : a –≫ b :=
    {
      epi_morphism := f
    }.
  Next Obligation. (* epi_morphism_epimorphism *)
  Proof.
    cut (g ∘ (f ∘ f⁻¹) = h ∘ (f ∘ f⁻¹)).
    {
      intros H'.
      rewrite right_inverse in H'; simpl_ids in H'; trivial.
    }
    {
      repeat rewrite <- assoc.
      rewrite H.
      reflexivity.
    }
  Qed.

End Iso_Mono_Epi.


