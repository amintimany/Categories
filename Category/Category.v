From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.

(** The basic definition of a category *)
Cumulative Record category : Type :=
{
  (** Type of Objects *)
  obj : Type;

  (** Type of morphism beween two objects *)
  hom : obj → obj → Type where "a → b" := (hom a b) : morphism_scope;

  (** composition of morphisms: *)
  compose : ∀ {a b c : obj}, (hom a b)%morphism → (hom b c) → (hom a c)
    where "f ∘ g" := (compose g f);

  (** associativity of composition: *)
  assoc : ∀ {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d),
            ((h ∘ g) ∘ f) = (h ∘ (g ∘ f));

  (** symmetric form of associativity: *)
  assoc_sym : ∀ {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d),
                ((h ∘ (g ∘ f) = (h ∘ g) ∘ f));

  (** identity morphisms: *)
  id : ∀ {a : obj}, hom a a;

  (** id left unit: *)
  left_id : ∀ (a b : obj) (h : hom a b), id ∘ h = h;

  (** id right unit: *)
  right_id : ∀ (a b : obj) (h : hom a b), h ∘ id = h
}.

Arguments obj {_}, _.
Arguments id {_ _}, {_} _, _ _.
Arguments hom {_} _ _, _ _ _.
Arguments compose {_} {_ _ _} _%_morphism _%_morphism.
Arguments assoc {_ _ _ _ _} _%_morphism _%_morphism _%_morphism.
Arguments assoc_sym {_ _ _ _ _} _%_morphism _%_morphism _%_morphism.
Arguments left_id {_ _ _} _%_morphism.
Arguments right_id {_ _ _} _%_morphism.

Notation "f ∘@{ C } g" := (@compose C _ _ _ g f) : morphism_scope.
Notation "f ∘ g" := (compose g f) : morphism_scope.

Bind Scope category_scope with category.

Bind Scope morphism_scope with hom.

Bind Scope object_scope with obj.

Coercion obj : category >-> Sortclass.

Hint Resolve left_id right_id : core.

(* basic tactics for categories *)

Ltac simpl_ids :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J; clear J | trivial]
  in
  repeat(
      match goal with
        | [|- context[(?A ∘ id)%morphism] ] => rewrite left_id
        | [|- context[(id ∘ ?A)%morphism] ] => rewrite right_id
        | [|- (?A ∘ ?B)%morphism = ?A] => id_detected B
        | [|- (?A = ?A ∘ ?B) %morphism] => id_detected B
        | [|- (?B ∘ ?A = ?A)%morphism] => id_detected B
        | [|- (?A = ?B ∘ ?A)%morphism] => id_detected B
      end
    ).

Ltac simpl_ids_in_I I :=
  repeat(
      match type of I with
        | context[(?A ∘ id)%morphism] => rewrite right_id in I
        | context[(id ∘ ?A)%morphism] => rewrite left_id in I
      end
    ).

Tactic Notation "simpl_ids" := simpl_ids.

Tactic Notation "simpl_ids" "in" hyp(I) := simpl_ids_in_I I.

Hint Extern 1 => progress simpl_ids : core.

Hint Extern 3 => progress (dohyps (fun H => simpl_ids in H)) : core.

Hint Extern 2 =>
match goal with
    [|- ?A = ?B :> hom _ _ _] =>
    repeat rewrite assoc; trivial; fail
end : core.

Hint Extern 2 =>
match goal with
  [H : _ = _ :> hom _ _ _ |- _ = _ :> hom _ _ _] =>
  repeat rewrite assoc in H;
    repeat rewrite assoc;
    (idtac + symmetry); apply H
end : core.

Definition hom_trans {C : category} {a b c d : C} (eqd : a = b) (eqc : c = d) (h : hom a c) : hom b d :=
  match eqd in _ = y return hom y d with
  eq_refl => match eqc in _ = z return hom a z with eq_refl => h end
  end.

Arguments hom_trans : simpl never.

Lemma hom_trans_refl {C : category} {a c : C} (eqd : a = a) (eqc : c = c) (h : hom a c) : hom_trans eqd eqc h = h.
Proof.
  replace eqd with (eq_refl a); [|by apply proof_irrelevance].
  replace eqc with (eq_refl c); [done|by apply proof_irrelevance].
Qed.

Lemma hom_trans_trans {C : category} {a b c d e f : C} (eqd1 : a = b) (eqd2 : b = c) (eqc1 : d = e) (eqc2 : e = f) (h : hom a d) :
  hom_trans eqd2 eqc2 (hom_trans eqd1 eqc1 h) = (hom_trans (eq_trans eqd1 eqd2) (eq_trans eqc1 eqc2) h).
Proof. destruct eqd1; destruct eqd2; destruct eqc1; destruct eqc2; done. Qed.

Lemma hom_trans_comp_take_in_l {C : category} {a b c d x : C} (eqd : a = b) (eqc : c = d) (g : hom d x) (h : hom a c) :
  (g ∘ hom_trans eqd eqc h = hom_trans eqd eq_refl ((hom_trans (eq_sym eqc) eq_refl g) ∘ h))%morphism.
Proof. destruct eqd; destruct eqc; done. Qed.

Lemma hom_trans_comp_take_in_r {C : category} {a b c d x : C} (eqd : c = b) (eqc : d = x) (g : hom c d) (h : hom a b) :
  ((hom_trans eqd eqc g) ∘ h = hom_trans eq_refl eqc (g ∘ (hom_trans eq_refl (eq_sym eqd) h)))%morphism.
Proof. destruct eqd; destruct eqc; done. Qed.

Lemma hom_trans_comp_split {C : category} {a b c x y : C} (eqd : a = b) (eqc : x = y) (g : hom c x) (h : hom a c) :
  (hom_trans eqd eqc (g ∘ h) = hom_trans eq_refl eqc g ∘ hom_trans eqd eq_refl h)%morphism.
Proof. destruct eqd; destruct eqc; done. Qed.

Lemma hom_trans_l_to_r {C : category} {a b c d : C} (eqd : a = b) (eqc : c = d) (g : hom a c) (h : hom b d) :
  g = hom_trans (eq_sym eqd) (eq_sym eqc) h → hom_trans eqd eqc g = h.
Proof. destruct eqd; destruct eqc; done. Qed.

Lemma hom_trans_r_to_l {C : category} {a b c d : C} (eqd : a = b) (eqc : c = d) (g : hom a c) (h : hom b d) :
  hom_trans (eq_sym eqd) (eq_sym eqc) h = g → h = hom_trans eqd eqc g.
Proof. destruct eqd; destruct eqc; done. Qed.