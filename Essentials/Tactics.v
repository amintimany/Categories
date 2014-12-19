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
(*
Lemma JMeq_prod {A B C D: Type} {x : A} {y : B} {x' : C} {y' : D} : x ≃ x' → y ≃ y' → (x, y) ≃ (x', y').
Proof.
  intros [] []; trivial.
Qed.

Hint Extern 1 ((_, _) ≃ (_, _)) => apply JMeq_prod.

*)

(* Tactics to apply a tactic to all hypothesis in an effiecient way. This is due to Jonathan's (jonikelee@gmail.com) message on coq-club *)


Ltac revert_clearbody_all :=
 repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac hyp_stack :=
 constr:($(revert_clearbody_all;constructor)$ : True).

Ltac next_hyp hs step last :=
 lazymatch hs with (?hs' ?H) => step H hs' | _ => last end.

Tactic Notation "dohyps" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H; next_hyp hs step idtac in
 next_hyp hs step idtac.

Tactic Notation "dohyps" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step idtac; tac H in
 next_hyp hs step idtac.

Tactic Notation "do1hyp" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H + next_hyp hs step fail in
 next_hyp hs step fail.

Tactic Notation "do1hyp" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step fail + tac H in
 next_hyp hs step fail.

(* End of tactics for applying a tactic to all hypothesis. *)
