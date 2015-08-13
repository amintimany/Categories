Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Category.
Require Import Category.Opposite.

Local Open Scope morphism_scope.

(** The basic Definition of an isomorphism in a category.
An isomorphism is a pair of arrows f : a -> b and g : b -> a such that g ∘ f = id a and f ∘ g = id b. *)
Record Isomorphism {C : Category} (a b : C) : Type := 
{
  iso_morphism : a –≻ b;
  
  inverse_morphism : b –≻ a;
  
  left_inverse : (inverse_morphism ∘ iso_morphism)%morphism = id;
  
  right_inverse : (iso_morphism ∘ inverse_morphism)%morphism = id
}.


Bind Scope morphism_scope with Isomorphism.
Bind Scope isomorphism_scope with Isomorphism.

Hint Resolve left_inverse.

Hint Resolve right_inverse.

Coercion iso_morphism : Isomorphism >-> Hom.

Arguments iso_morphism {_ _ _} _.
Arguments inverse_morphism {_ _ _} _.
Arguments left_inverse {_ _ _} _.
Arguments right_inverse {_ _ _} _.

Notation "f '⁻¹'" := (inverse_morphism f) : morphism_scope.

Notation "a ≃ b" := (Isomorphism a b) : isomorphism_scope.

Notation "a ≃≃ b ::> C" := (@Isomorphism C a b) : isomorphism_scope.

Local Open Scope isomorphism_scope.

(* basic tactics for isomorphisms *)

Ltac simpl_isos_in_goal :=
  repeat(
      match goal with
        | [|- context[(iso_morphism ?A ∘ inverse_morphism ?A)%morphism]] => rewrite (right_inverse A); simpl_ids
        | [|- context[(inverse_morphism ?A ∘ iso_morphism ?A)%morphism] ] => rewrite (left_inverse A); simpl_ids
(* disabled due to problems with reveal_comp complexity *)
(*        | [|- context[iso_morphism ?A] ] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) +
          reveal_comp (iso_morphism A) (inverse_morphism A) *)
      end
    )
.

Ltac simpl_isos_in_I I :=
  repeat(
      match type of I with
        | context[(iso_morphism ?A ∘ inverse_morphism ?A)%morphism] => rewrite (right_inverse A) in I; simpl_ids in I
        | context[(inverse_morphism ?A ∘ iso_morphism ?A)%morphism] => rewrite (left_inverse A) in I; simpl_ids in I
(* disabled due to problems with reveal_comp complexity *)
(*        | context[inverse_morphism ?A] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) in I +
          reveal_comp (iso_morphism A) (inverse_morphism A) in I *)
      end
    )
.

Tactic Notation "simpl_isos" := simpl_isos_in_goal.

Tactic Notation "simpl_isos" "in" hyp(I) := simpl_isos_in_I I.

Hint Extern 3 => progress simpl_isos.

Hint Extern 3 => progress (dohyps (fun H => simpl_isos in H)).

(** simplifies equality of iso-morphisms. This theorem uses proof irrelevance to assume any two proofs for left and right inverse properties are equal.
In other words, two isomorphisms are equal if their underlying morphisms are. *)
Theorem Isomorphism_eq_simplify {C : Category} {a b : C} (I I' : a ≃ b) : (iso_morphism I = iso_morphism I') → (inverse_morphism I = inverse_morphism I') → I = I'.
Proof.
  intros H1 H2.
  destruct I as [iI inI Il Ir]; destruct I' as [iI' inI' Il' Ir'].
  cbn in *.
  destruct H1; destruct H2.
  destruct (proof_irrelevance _ Il Il').
  destruct (proof_irrelevance _ Ir Ir').
  trivial.  
Qed.  

(** Isomorphism is an equivalence relation on objects. *)

(** The identity morphism forms an isomorphism, i.e., it is inverse to itself.
This is reflexivity property for the equivalence relation of isomorphism on objects. *)
Program Definition Isomorphism_id {C : Category} {a : C} : a ≃ a :=
{|
  iso_morphism := id;
  inverse_morphism := id
|}.

(** Each ismorphism has an inverse isomorphism. Simply swap the morphisms and proofs of left and right inverse properties.
This is symmetry property for the equivalence relation of isomorphism on objects. *)
Definition Inverse_Isomorphism {C : Category} {a b : C} (I : a ≃ b) : b ≃ a :=
{|
  iso_morphism := I⁻¹;
  inverse_morphism := I;
  left_inverse := right_inverse I;
  right_inverse := left_inverse I
|}.

Notation "f '⁻¹'" := (Inverse_Isomorphism f) : isomorphism_scope.

(** Isomorphisms compose. Simply compose the underlying morphisms of the isomorphism. Left and right inverse properties follow straightforwardly.
This is transitivty property for the equivalence relation of isomorphism on objects. *)
Program Definition Isomorphism_Compose
        {C : Category} {a b c : C} (I : a ≃ b) (I' : b ≃ c) : a ≃ c
  :=
{|
  iso_morphism := I' ∘ I;
  inverse_morphism := I⁻¹ ∘ I'⁻¹
|}.

Next Obligation.
Proof.
  rewrite assoc.
  rewrite (assoc_sym I).
  auto.
Qed.

Next Obligation.
Proof.
  rewrite assoc.
  rewrite (assoc_sym I'⁻¹).
  auto.
Qed.

Notation "f ∘ g" := (Isomorphism_Compose g f) : isomorphism_scope.

(** A monic arrow (AKA, mono, monomorphic arrow and monomorphism) m is an arrow such that for any two arrows g and h (of the appropriate domain and codomain) we have if m ∘ g = m ∘ h then g = h. *)
Record Monic {C : Category} (a b : Obj) :=
{
  mono_morphism : a –≻ b;
  mono_morphism_monomorphic : ∀ (c : Obj) (g h : c –≻ a), (mono_morphism ∘ g = mono_morphism ∘ h)%morphism → g = h
}.

Coercion mono_morphism : Monic >-> Hom.

Arguments mono_morphism {_ _ _} _.
Arguments mono_morphism_monomorphic {_ _ _} _ _ _ _ _.

Notation "a ≫–> b" := (Monic a b) : morphism_scope.

Bind Scope morphism_scope with Monic.

(** An epic arrow (AKA, epi, epimorphic arrow and epimorphism) is a monomorphism in the opposite category. That is, m is epic if for any pair of arrows g and h (of the appropriate domain and codomain) we have if g ∘ m = h ∘ m then g = h. *)
Definition Epic {C : Category} (a b : C) := @Monic (C^op) b a.

Notation "a –≫ b" := (Epic a b) : morphism_scope.

Bind Scope morphism_scope with Epic.

(** Monomorphisms compose. The case for epis follows by duality.*)
Section Mono_compose.
  Context {C : Category} {a b c : C} (M : a ≫–> b) (M' : b ≫–> c).

  Local Hint Resolve mono_morphism_monomorphic.

  Local Obligation Tactic := eauto.
  
  Program Definition Mono_compose : a ≫–> c :=
    {|
      mono_morphism := M' ∘ M
    |}.
    
End Mono_compose.

(** An isomorphism is both monic and epic. *)
Section Iso_Mono_Epi.
  Context {C : Category} {a b : Obj} (I : a ≃ b).

  Program Definition Ismorphism_Monic : a ≫–> b :=
    {|
      mono_morphism := I
    |}.

  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    match goal with
        [ H : (_ ∘ ?f = _ ∘ ?f')%morphism |- ?f = ?f'] =>
        match type of H with
            ?A = ?B =>
            let H' := fresh "H" in
            cut (I⁻¹ ∘ A = I⁻¹ ∘ B)%morphism; [auto | rewrite H; trivial]
        end
    end.
    repeat rewrite assoc_sym.
    auto.
  Qed.

  Program Definition Ismorphism_Epic : b –≫ a :=
    {|
      mono_morphism := inverse_morphism I
    |}.
  Next Obligation. (* epi_morphism_epimorphism *)
  Proof.
    match goal with
        [ H : (?f ∘ _ = ?f' ∘ _)%morphism |- ?f = ?f'] =>
        match type of H with
            ?A = ?B =>
            let H' := fresh "H" in
            cut (A ∘ I = B ∘ I)%morphism; [auto | rewrite H; trivial]
        end
    end.
    repeat rewrite assoc.
    auto.
  Qed.

End Iso_Mono_Epi.

(** If two objects are isomorphic in category C then they are also isomorphic in C^op. *)
Theorem CoIso {C : Category} (a b : C) : a ≃≃ b ::> C → a ≃≃ b ::> C^op. 
Proof.
  intros I.
  eapply (Build_Isomorphism C^op _ _ I⁻¹ I); unfold compose; simpl; auto.
Qed.