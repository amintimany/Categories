Require Import Category.Category.
Require Import Category.Tactics.

Set Primitive Projections.

Set Universe Polymorphism.

Class Isomorphism `{C : Category} {a b : Obj} (f : Hom a b) : Type := 
{
  inverse_morphism : Hom b a;
  
  left_inverse : (inverse_morphism ∘ f) = id;
  
  right_inverse : (f ∘ inverse_morphism) = id
}.

Arguments inverse_morphism {_ _ _} _ {_}.

Notation "f '⁻¹'" := (inverse_morphism f) (at level 7, no associativity) : morphism_scope.

Instance Inverse_Isomorphism {C : Category} {a b : Obj} {f : Hom a b} (I : Isomorphism f) : Isomorphism (f⁻¹) :=
{
  inverse_morphism := f;
  left_inverse := right_inverse;
  right_inverse := left_inverse
}.

Program Instance Isomorphism_Compose {C : Category} {a b c : Obj} {f : Hom a b} {g : Hom b c} (I : Isomorphism f) (I' : Isomorphism g): Isomorphism (g ∘ f) :=
{
  inverse_morphism := (f⁻¹ ∘ g⁻¹)
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

Class Isomorphic {C : Category} (a b : Obj) :=
{
  iso_morphism : Hom a b;
  
  iso_morphism_isomorphism : Isomorphism iso_morphism
}.

Existing Instance iso_morphism_isomorphism.

Coercion iso_morphism_isomorphism : Isomorphic >-> Isomorphism.

Notation "a ≡ b" := (Isomorphic a b) (at level 70, no associativity).

Section Isomorphic_equiv.
  Context {C : Category} (a b c : Obj).
    
  Theorem Isomorphic_refl : a ≡ a.
  Proof.
    do 2 exists id; auto.
  Qed.
  
  Theorem Isomorphic_sym : a ≡ b → b ≡ a.
  Proof.
    intros I.
    eapply (Build_Isomorphic _ _ _ _ (Inverse_Isomorphism I)).
  Qed.
  
  Theorem Isomorphic_trans : a ≡ b → b ≡ c → a ≡ c.
  Proof.
    intros I I'.
    eapply (Build_Isomorphic _ _ _ _ (Isomorphism_Compose I I')).
  Qed.
  
  Hint Resolve Isomorphic_refl Isomorphic_trans.
  Hint Immediate Isomorphic_sym.
End Isomorphic_equiv.


Class Monic {C : Category} (a b : Obj) :=
{
  mono_morphism : Hom a b;
  mono_morphism_monomorphism : ∀ (c : Obj) (g h : Hom c a), mono_morphism ∘ g = mono_morphism ∘ h → g = h
}.

Class Epic {C : Category} (a b : Obj) :=
{
  epi_morphism : Hom a b;
  epi_morphism_epimorphism : ∀ (c : Obj) (g h : Hom b c), g ∘ epi_morphism = h ∘ epi_morphism -> g = h
}.

Notation "a ≫–> b" := (Monic a b).

Notation "a –≫ b" := (Epic a b).

Section Iso_Mono_Epi.
  Context {C : Category} {a b : Obj} (f : Hom a b) (I : Isomorphism f).

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
(*      rewrite H.
      reflexivity. *)
      admit.
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
      (* rewrite H.
      reflexivity. *)
      admit.
    }
  Qed.

End Iso_Mono_Epi.


