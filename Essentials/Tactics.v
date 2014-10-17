Require Import Essentials.Notations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

(* Equality on sigma type under proof irrelevance *)

Lemma sig_proof_irrelevance {A : Type} (P : A → Prop) (x y : A) (Px : P x) (Py : P y) : x = y → exist P x Px = exist P y Py.
Proof.
  intros H.
  destruct H.
  destruct (proof_irrelevance _ Px Py).
  reflexivity.
Qed.

Hint Extern 2 (exist ?A _ _ = exist ?A _ _) => apply sig_proof_irrelevance.

Lemma JMeq_prod {A B C D: Type} {x : A} {y : B} {x' : C} {y' : D} : x ≃ x' → y ≃ y' → (x, y) ≃ (x', y').
Proof.
  intros [] []; trivial.
Qed.

Hint Extern 1 ((_, _) ≃ (_, _)) => apply JMeq_prod.


