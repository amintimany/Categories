Require Import Category.Category.
Require Import Category.Opposite.

Class Isomorphism {C : Category} (a b : C) : Type := 
{
  iso_morphism : Hom a b;
  
  inverse_morphism : Hom b a;
  
  left_inverse : (inverse_morphism ∘ iso_morphism) = id;
  
  right_inverse : (iso_morphism ∘ inverse_morphism) = id
}.

Hint Resolve left_inverse.

Hint Resolve right_inverse.

Coercion iso_morphism : Isomorphism >-> Hom.

Arguments iso_morphism {_ _ _} _.
Arguments inverse_morphism {_ _ _} _.
Arguments left_inverse {_ _ _} _.
Arguments right_inverse {_ _ _} _.

Notation "f '⁻¹'" := (inverse_morphism f) (at level 7, no associativity) : morphism_scope.

Notation "a ≡ b" := (Isomorphism a b) (at level 70, no associativity) : morphism_scope.

Notation "a ≡≡ b ::> C" := (@Isomorphism C a b) (at level 70, no associativity) : morphism_scope.

(* basic tactics for isomorphisms *)

Ltac simpl_isos_in_goal :=
  repeat(
      match goal with
        | [|- context[iso_morphism ?A ∘ inverse_morphism ?A]] => rewrite (right_inverse A); simpl_ids
        | [|- context[inverse_morphism ?A ∘ iso_morphism ?A] ] => rewrite (left_inverse A); simpl_ids
        | [|- context[iso_morphism ?A] ] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) +
          reveal_comp (iso_morphism A) (inverse_morphism A) 
      end
    )
.

Ltac simpl_isos_in_I I :=
  repeat(
      match type of I with
        | context[iso_morphism ?A ∘ inverse_morphism ?A] => rewrite (right_inverse A) in I; simpl_ids in I
        | context[inverse_morphism ?A ∘ iso_morphism ?A] => rewrite (left_inverse A) in I; simpl_ids in I
        | context[inverse_morphism ?A] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) in I +
          reveal_comp (iso_morphism A) (inverse_morphism A) in I
      end
    )
.

Tactic Notation "simpl_isos" := simpl_isos_in_goal.

Tactic Notation "simpl_isos" "in" hyp(I) := simpl_isos_in_I I.

Hint Extern 3 => progress simpl_isos.

Hint Extern 3 => progress (dohyps (fun H => simpl_isos in H)).

Theorem Isomorphism_eq_simplify {C : Category} {a b : C} (I I' : a ≡ b) : (iso_morphism I = iso_morphism I') → (inverse_morphism I = inverse_morphism I') → I = I'.
Proof.
  intros H1 H2.
  destruct I as [iI inI Il Ir]; destruct I' as [iI' inI' Il' Ir'].
  cbn in *.
  destruct H1; destruct H2.
  destruct (proof_irrelevance _ Il Il').
  destruct (proof_irrelevance _ Ir Ir').
  trivial.  
Qed.  

(* Isomorphism is an equivalence relation *)

Program Instance Isomorphism_id {C : Category} {a : C} : a ≡ a :=
{
  iso_morphism := id;
  inverse_morphism := id
}.

Instance Inverse_Isomorphism {C : Category} {a b : C} (I : a ≡ b) : b ≡ a :=
{
  iso_morphism := I⁻¹;
  inverse_morphism := I;
  left_inverse := right_inverse I;
  right_inverse := left_inverse I
}.

Program Instance Isomorphism_Compose {C : Category} {a b c : C} (I : a ≡ b) (I' : b ≡ c) : a ≡ c :=
{
  iso_morphism := I' ∘ I;
  inverse_morphism := I⁻¹ ∘ I'⁻¹
}.

Class Monic {C : Category} (a b : Obj) :=
{
  mono_morphism : Hom a b;
  mono_morphism_monomorphic : ∀ (c : Obj) (g h : Hom c a), mono_morphism ∘ g = mono_morphism ∘ h → g = h
}.

Arguments mono_morphism {_ _ _} _.
Arguments mono_morphism_monomorphic {_ _ _} _ _ _ _ _.

Notation "a ≫–> b" := (Monic a b).

Definition Epic {C : Category} (a b : C) := @Monic (C^op) b a.

Existing Class Epic.

Notation "a –≫ b" := (Epic a b).

Section Iso_Mono_Epi.
  Context {C : Category} {a b : Obj} (I : a ≡ b).

  Program Instance Ismorphism_Monic : a ≫–> b :=
    {
      mono_morphism := I
    }.
  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    match goal with
        [ H : _ ∘ ?f = _ ∘ ?f' |- ?f = ?f'] =>
        match type of H with
            ?A = ?B =>
            let H' := fresh "H" in
            cut (I⁻¹ ∘ A = I⁻¹ ∘ B); [auto | rewrite H; trivial]
        end
    end.
  Qed.

  Program Instance Ismorphism_Epic : b –≫ a :=
    {|
      mono_morphism := inverse_morphism I
    |}.
  Next Obligation. (* epi_morphism_epimorphism *)
  Proof.
    match goal with
        [ H : ?f ∘ _ = ?f' ∘ _ |- ?f = ?f'] =>
        match type of H with
            ?A = ?B =>
            let H' := fresh "H" in
            cut (A ∘ I = B ∘ I); [auto | rewrite H; trivial]
        end
    end.
  Qed.

End Iso_Mono_Epi.

Theorem CoIso {C : Category} (a b : C) : a ≡≡ b ::> C → a ≡≡ b ::> C^op. 
Proof.
  intros I.
  eapply (Build_Isomorphism C^op _ _ I⁻¹ I); unfold compose; simpl; auto.
Qed.