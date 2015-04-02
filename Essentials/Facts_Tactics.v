Require Import Essentials.Notations.

Require Export Coq.Program.Tactics.
Require Export Coq.Program.Equality.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Set Universe Polymorphism.

(* Equality on sigma type under proof irrelevance *)

Lemma sig_proof_irrelevance {A : Type} (P : A → Prop) (x y : A) (Px : P x) (Py : P y) : x = y → exist P x Px = exist P y Py.
Proof.
  intros H.
  destruct H.
  destruct (proof_irrelevance _ Px Py).
  reflexivity.
Qed.

Hint Extern 2 (exist ?A _ _ = exist ?A _ _) => apply sig_proof_irrelevance.

Lemma pair_JM_eq (A B C D : Type) (a : A * B) (c : C * D) : fst a ≃ fst c → snd a ≃ snd c → a ≃ c.
Proof.
  intros H1 H2.
  dependent destruction H1; dependent destruction H2.
  cutrewrite (a = c); trivial.
  destruct a; destruct c;
  simpl in *;
  repeat match goal with [H : _ = _|-_] => rewrite H end; trivial.
Qed.

Lemma pair_eq (A B : Type) (a b : A * B) : fst a = fst b → snd a = snd b → a = b.
Proof.
  intros H1 H2.
  destruct a; destruct b;
  simpl in *;
  repeat match goal with [H : _ = _|-_] => rewrite H end; trivial.
Qed.

Ltac JMeqToEq :=
  match goal with
    [|- ?A ~= ?B] =>
    let H := fresh in
    cut (A = B); [intros H; rewrite H; trivial|]
  end.

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
