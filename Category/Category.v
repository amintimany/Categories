Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Require Export Essentials.Notations.
Require Export Essentials.Tactics.

Class Category (Obj : Type) (Hom : Obj → Obj → Type) : Type :=
{
  (* composition of morphisms: *)
  compose : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c where "f ∘ g" := (compose g f);

  (* associativity of composition: *)
  assoc : ∀ {a b c d : Obj} (f : Hom  a b) (g : Hom b c) (h : Hom c d),
                     ((h ∘ g) ∘ f) = (h ∘ (g ∘ f));

  (* symmetric form of associativity: *)
  assoc_sym : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
                     ((h ∘ (g ∘ f) = (h ∘ g) ∘ f));

  (* identity morphisms: *)
  id : ∀ {a : Obj}, Hom a a;

  (* id left unit: *)
  id_unit_left : ∀ (a b : Obj) (h : Hom a b), id ∘ h = h;

  (* id right unit: *)
  id_unit_right : ∀ (a b : Obj) (h : Hom a b), h ∘ id = h
}.

Notation "f ∘ g" := (compose g f) : morphism_scope.

(* Allowing variables Obj and Hom be generalizable anywhere we work with categories *)

Global Generalizable Variables Obj Hom.

Hint Resolve id_unit_left id_unit_right.

Lemma Category_eq_simplify `(C : Category Obj Hom) `(C' : Category Obj' Hom') : Obj = Obj' → Hom ≃ Hom' → @compose _ _ C ≃ @compose _ _ C' → @id _ _ C ≃ @id _ _ C' → C ≃ C'.
Proof.
  intros H1 H2 H3 H4.
  destruct C as [Ccomp Cas Cass Cid Ciul Ciur]; destruct C' as [Ccomp' Cas' Cass' Cid' Ciul' Ciur']; simpl in *.
  destruct H1.
  dependent destruction H2.
  dependent destruction H3.
  dependent destruction H4.
  destruct (proof_irrelevance _ Cas Cas').
  destruct (proof_irrelevance _ Cass Cass').
  destruct (proof_irrelevance _ Ciul Ciul').
  destruct (proof_irrelevance _ Ciur Ciur').
  reflexivity.
Qed.



