From Categories.Essentials Require Import Notations Facts_Tactics.
From Coq.Logic Require Import ChoiceFacts ClassicalFacts.

From Coq.Classes Require Import RelationClasses.

Local Axiom PropExt : ClassicalFacts.prop_extensionality.
Local Axiom ConstructiveIndefiniteDescription_Type :
  forall T : Type, ConstructiveIndefiniteDescription_on T.

Record EquiRel A :=
  { EQR_rel :> A → A → Prop;
    EQR_EQ : Equivalence EQR_rel }.

Existing Instances EQR_EQ.

Section Quotient.
  Context {A : Type} (R : EquiRel A).

  Definition quotient : Type := {P : A → Prop | ∃ x, ∀ y, P y ↔ R x y }.

  Definition represents (c : quotient) (x : A) : Prop := proj1_sig c x.

  Lemma represented_rel c x y :
    represents c x → represents c y → R x y.
  Proof.
    intros Hx Hy.
    pose proof (proj2_sig c) as [z Hz].
    transitivity z; [symmetry|]; apply Hz; trivial.
  Qed.

  Lemma related_represented c x y :
    represents c x → R x y → represents c y.
  Proof.
    intros Hx Hxy.
    pose proof (proj2_sig c) as [z Hz].
    apply Hz.
    transitivity x; [|trivial].
    apply Hz; trivial.
  Qed.

  Lemma quotient_has_representative c : ∃ x, represents c x.
  Proof.
    destruct c as [P [y Hy]].
    exists y; apply Hy; reflexivity.
  Qed.

  Lemma uniquely_represented c c' x y :
    represents c x → represents c' y → R x y → c = c'.
  Proof.
    intros Hcx Hc'y Hxy.
    apply sig_proof_irrelevance.
    extensionality z.
    apply PropExt.
    pose proof (proj2_sig c) as [u Hu].
    pose proof (proj2_sig c') as [w Hw].
    split.
    - intros Hc%Hu; apply Hw.
      etransitivity; [|apply Hc].
      etransitivity; [apply (Hw y); trivial|].
      symmetry; etransitivity; [apply (Hu x); trivial|trivial].
    - intros Hc'%Hw; apply Hu.
      etransitivity; [|apply Hc'].
      etransitivity; [apply (Hu x); trivial|].
      symmetry; etransitivity; [apply (Hw y); trivial|symmetry; trivial].
  Qed.

  Definition representative (c : quotient) : A :=
    proj1_sig
      (ConstructiveIndefiniteDescription_Type
         _ _ (quotient_has_representative c)).

  Lemma representative_represented c : represents c (representative c).
  Proof.
    exact (proj2_sig (ConstructiveIndefiniteDescription_Type
                        _ _ (quotient_has_representative c))).
  Qed.

  Definition class_of (x : A) : quotient :=
    exist _ (λ y, R x y) (ex_intro _ x (λ z, (conj (@id (R x z)) (@id (R x z))))).

  Lemma class_of_represents x : represents (class_of x) x.
  Proof. unfold represents; simpl; reflexivity. Qed.

  Lemma representative_of_class_of x : R (representative (class_of x)) x.
  Proof.
    eapply represented_rel; [apply representative_represented|].
    apply class_of_represents.
  Qed.

  Lemma class_of_inj x y : R x y → class_of x = class_of y.
  Proof.
    intros Hxy.
    apply (uniquely_represented _ _ x y);
      [apply class_of_represents|apply class_of_represents |trivial].
  Qed.

  Lemma class_of_representative c : class_of (representative c) = c.
  Proof.
    apply (uniquely_represented _ _ (representative c) (representative c));
      [| |reflexivity].
    - apply class_of_represents.
    - apply representative_represented.
  Qed.

End Quotient.

Arguments represents {_ _} _ _.
Arguments representative {_ _} _.
