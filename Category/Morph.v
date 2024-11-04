From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category.
From Categories Require Import Category.Opposite.

(** The basic Definition of an isomorphism in a category.
An isomorphism is a pair of arrows f : a -> b and g : b -> a such that
g ∘ f = id a and f ∘ g = id b. *)
Record Isomorphism {C : category} (a b : C) : Type :=
{
  iso_morphism : hom a b;

  inverse_morphism : hom b a;

  left_inverse : (inverse_morphism ∘ iso_morphism)%morphism = id;

  right_inverse : (iso_morphism ∘ inverse_morphism)%morphism = id
}.


Bind Scope morphism_scope with Isomorphism.
Bind Scope isomorphism_scope with Isomorphism.

Hint Resolve left_inverse : core.

Hint Resolve right_inverse : core.

Coercion iso_morphism : Isomorphism >-> hom.

Arguments iso_morphism {_ _ _} _.
Arguments inverse_morphism {_ _ _} _.
Arguments left_inverse {_ _ _} _.
Arguments right_inverse {_ _ _} _.

Notation "f '⁻¹'" := (inverse_morphism f) : morphism_scope.

Notation "a ≃ b" := (Isomorphism a b) : type_scope.

Notation "a ≃@{ C } b" := (@Isomorphism C a b) : type_scope.

(* basic tactics for isomorphisms *)

Ltac simpl_isos_in_goal :=
  repeat(
      match goal with
      | [|- context[(iso_morphism ?A ∘ inverse_morphism ?A)%morphism]] =>
        rewrite (right_inverse A); simpl_ids
      | [|- context[(inverse_morphism ?A ∘ iso_morphism ?A)%morphism] ] =>
        rewrite (left_inverse A); simpl_ids
(* disabled due to problems with reveal_comp complexity *)
(*        | [|- context[iso_morphism ?A] ] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) +
          reveal_comp (iso_morphism A) (inverse_morphism A) *)
      end
    ).

Ltac simpl_isos_in_I I :=
  repeat(
      match type of I with
      | context[(iso_morphism ?A ∘ inverse_morphism ?A)%morphism] =>
        rewrite (right_inverse A) in I; simpl_ids in I
      | context[(inverse_morphism ?A ∘ iso_morphism ?A)%morphism] =>
        rewrite (left_inverse A) in I; simpl_ids in I
(* disabled due to problems with reveal_comp complexity *)
(*        | context[inverse_morphism ?A] =>
          reveal_comp (inverse_morphism A) (iso_morphism A) in I +
          reveal_comp (iso_morphism A) (inverse_morphism A) in I *)
      end
    ).

Tactic Notation "simpl_isos" := simpl_isos_in_goal.

Tactic Notation "simpl_isos" "in" hyp(I) := simpl_isos_in_I I.

Hint Extern 3 => progress simpl_isos : core.

Hint Extern 3 => progress (dohyps (fun H => simpl_isos in H)) : core.

(** simplifies equality of iso-morphisms. This theorem uses proof irrelevance
to assume any two proofs for left and right inverse properties are equal.
In other words, two isomorphisms are equal if their underlying morphisms are. *)
Theorem Isomorphism_eq_simplify {C : category} {a b : C} (I I' : a ≃ b) :
  (iso_morphism I = iso_morphism I') →
  (inverse_morphism I = inverse_morphism I') → I = I'.
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
This is reflexivity property for the equivalence relation of isomorphism
on objects. *)
Program Definition Isomorphism_id {C : category} {a : C} : a ≃ a :=
{|
  iso_morphism := id;
  inverse_morphism := id
|}.
Next Obligation.
Proof. intros ??; rewrite left_id //. Qed.
Next Obligation.
Proof. intros ??; rewrite right_id //. Qed.
Fail Next Obligation.

(** Each ismorphism has an inverse isomorphism. Simply swap the morphisms and
proofs of left and right inverse properties. This is symmetry property for the
equivalence relation of isomorphism on objects. *)
Definition Inverse_Isomorphism {C : category} {a b : C} (I : a ≃ b) : b ≃ a :=
{|
  iso_morphism := I⁻¹;
  inverse_morphism := I;
  left_inverse := right_inverse I;
  right_inverse := left_inverse I
|}.

Notation "f '⁻¹'" := (Inverse_Isomorphism f) : isomorphism_scope.

(** Isomorphisms compose. Simply compose the underlying morphisms of the 
isomorphism. Left and right inverse properties follow straightforwardly.
This is transitivty property for the equivalence relation of isomorphism
on objects. *)
Program Definition Isomorphism_Compose {C : category} {a b c : C} (I : a ≃ b) (I' : b ≃ c) :
  (a ≃ c)%isomorphism :=
{|
  iso_morphism := I' ∘ I;
  inverse_morphism := I⁻¹ ∘ I' ⁻¹
|}.
Next Obligation.
Proof.
  intros ???? I ?; rewrite assoc (assoc_sym I) left_inverse left_id left_inverse //.
Qed.
Next Obligation.
Proof.
  intros ????? I'; rewrite assoc (assoc_sym (I' ⁻¹)) right_inverse left_id right_inverse //.
Qed.
Fail Next Obligation.

Notation "f ∘ g" := (Isomorphism_Compose g f) : isomorphism_scope.

(** A monic arrow (AKA, mono, monomorphic arrow and monomorphism) m is an arrow
such that for any two arrows g and h (of the appropriate domain and codomain)
we have if m ∘ g = m ∘ h then g = h. *)
Record Monic {C : category} (a b : C) :=
  {
    mono_morphism : hom a b;
    mono_morphism_monomorphic : ∀ (c : C) (g h : hom c a),
      (mono_morphism ∘ g = mono_morphism ∘ h)%morphism → g = h
  }.

Coercion mono_morphism : Monic >-> hom.

Arguments mono_morphism {_ _ _} _.
Arguments mono_morphism_monomorphic {_ _ _} _ _ _ _ _.

Notation "a ≫–> b" := (Monic a b) : type_scope.

(** An epic arrow (AKA, epi, epimorphic arrow and epimorphism) is a monomorphism
in the opposite category. That is, m is epic if for any pair of arrows g and h
(of the appropriate domain and codomain) we have if g ∘ m = h ∘ m then g = h. *)
Definition Epic {C : category} (a b : C) := @Monic (C ᴼᴾ) b a.

Notation "a –≫ b" := (Epic a b) : type_scope.

(** The condition for a morphism to be mono-morphic. *)
Definition is_Monic {C : category} {a b : C} (f : hom a b) := ∀ (c : C) (g h : hom c a), (f ∘ g = f ∘ h)%morphism → g = h.

(** A mono-morphic morphism forms a Monic. *)
Definition is_Monic_Monic {C : category} {a b : C} {f : hom a b} (M : is_Monic f) : Monic a b :=
  {|
    mono_morphism := f;
    mono_morphism_monomorphic := M
  |}.

(** A morphism is ipic if it is monic in the opposit category. *)
Definition is_Epic {C : category} {a b : C} (f : hom a b) := @is_Monic (C ᴼᴾ) b a f.

(** A morphism f : a --> b is split monic if there is another morphism
g : b --> a such that g ∘ f = idₐ *)
Record is_split_Monic {C : category} {a b : C} (f : hom a b) :=
  {
    is_split_monic_left_inverse : hom b a;
    is_split_monic_left_inverse_is_left_inverse :
      (is_split_monic_left_inverse ∘ f)%morphism = id
  }.

Arguments is_split_monic_left_inverse {_ _ _ _} _.
Arguments is_split_monic_left_inverse_is_left_inverse {_ _ _ _} _.

(** A morphism is ipic if it is monic in the opposit category. *)
Definition is_split_Epic {C : category} {a b : C} (f : hom a b) := @is_split_Monic (C ᴼᴾ) b a f.

(** A split monic morphism is a monomorphism. *)
Program Definition is_split_Monic_Monic {C : category} {a b : C} {f : hom a b} (SM : is_split_Monic f) : Monic a b :=
  {|
    mono_morphism := f;
    mono_morphism_monomorphic := _
  |}.
Next Obligation.
Proof. intros ???? [r Hr] ??? Hgh; rewrite -(left_id g) -(left_id h) -!Hr !assoc Hgh //. Qed.
Fail Next Obligation.

(** If a monic morphism is split epic, it forms an isomorphism. *)
Program Definition Monic_is_split_Epic_Iso {C : category} (a b : C) (f : a ≫–> b) (SE : is_split_Epic f) : (a ≃ b)%isomorphism
  :=
    {|
      iso_morphism := f;
      inverse_morphism := is_split_monic_left_inverse SE;
      right_inverse := is_split_monic_left_inverse_is_left_inverse SE
    |}.
Next Obligation.
Proof.
  intros ??? f SE.
  apply (mono_morphism_monomorphic f).
  rewrite assoc_sym.
  cbn_rewrite (is_split_monic_left_inverse_is_left_inverse SE); auto.
Qed.
Fail Next Obligation.

(** If both g and (f ∘ g) are monic, then so is f. *)
Program Definition Compose_Monic_is_Monic_then_Monic {C : category} {a b c : C} (M : hom a b) (M' : b ≫–> c)
  (iM : is_Monic (M' ∘ M)) : Monic a b
  :=
    {|
      mono_morphism := M;
      mono_morphism_monomorphic := _
    |}.
Next Obligation.
Proof. intros ?????? iM ??? Hgh; apply iM; rewrite !assoc Hgh //. Qed.
Fail Next Obligation.

(** Monomorphisms compose. The case for epis follows by duality.*)
Program Definition Mono_compose {C : category} {a b c : C} (M : a ≫–> b) (M' : b ≫–> c) : a ≫–> c :=
  {|
    mono_morphism := M' ∘ M
  |}.
Next Obligation.
Proof. eauto using mono_morphism_monomorphic. Qed.
Fail Next Obligation.

(** An isomorphism is both monic and epic. *)
Program Definition Ismorphism_Monic {C : category} {a b : C} (I : a ≃ b) : a ≫–> b :=
  {|
    mono_morphism := I
  |}.
  Next Obligation. (* mono_morphism_monomorphism *)
  Proof.
    intros ????????.
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

  Program Definition Ismorphism_Epic {C : category} {a b : C} (I : a ≃ b) : b –≫ a :=
    {|
      mono_morphism := inverse_morphism I
    |}.
  Next Obligation. (* epi_morphism_epimorphism *)
  Proof.
    intros ????????; cbn in *.
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

(** If two objects are isomorphic in category C then they are also isomorphic
in C^op. *)
Theorem CoIso {C : category} (a b : C) : a ≃@{C} b → a ≃@{C ᴼᴾ} b.
Proof.
  intros I.
  eapply (Build_Isomorphism (C ᴼᴾ)%category _ _ (I⁻¹) I);
    unfold compose; simpl; auto.
Qed.
