From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.

Require Export Coq.Program.Tactics.
Require Export Coq.Program.Equality.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

From Coq.ssr Require Export ssreflect.

Definition equal_f_dep [A : Type] [B : A → Type] [f g : ∀ x, B x] : f = g → ∀ x : A, f x = g x :=
  fun eq x => match eq in _ = u return f x = u x with eq_refl => eq_refl end.
Definition equal_f [A B : Type] [f g : A → B] : f = g → ∀ x : A, f x = g x :=
  fun eq x => equal_f_dep eq x.

Definition f_equal [A B : Type] (f : A → B) [x y : A] : x = y → f x = f y :=
  fun eq => match eq in _ = z return f x = f z with eq_refl => eq_refl end.

Lemma equal_f_dep_eq_sym [A : Type] [B : A → Type] [f g : ∀ x, B x] (fgeq : f = g) :
  ∀ x : A, equal_f_dep (eq_sym fgeq) x = eq_sym (equal_f_dep fgeq x).
Proof. destruct fgeq; done. Qed.

Lemma equal_f_eq_sym [A B : Type] [f g : A → B] (fgeq : f = g) :
  ∀ x : A, equal_f (eq_sym fgeq) x = eq_sym (equal_f fgeq x).
Proof. destruct fgeq; done. Qed.

Lemma f_equal_eq_sym [A B : Type] (f : A → B) [x y : A] (xyeq : x = y) :
  f_equal f (eq_sym xyeq) = eq_sym (f_equal f xyeq).
Proof. destruct xyeq; done. Qed.

Ltac basic_simpl :=
  let simpl_prod _ :=
      match goal with
        [H : prod _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let simpl_sig _ :=
      match goal with
        [H : @sig _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let basic_simpl_helper _ :=
      cbn in *; intros;
        repeat simpl_prod tt;
        repeat simpl_sig tt
  in
  repeat basic_simpl_helper tt
.

Global Obligation Tactic := idtac.

(** A tactic to apply proof irrelevance on all proofs of the same type in the
 context. *)
Ltac PIR :=
  let pir_helper _ :=
      match goal with
      |[H : ?A, H' : ?A|- _] =>
       match type of A with
       | Prop =>
         destruct (proof_irrelevance _ H H')
       end
      end
  in
  repeat pir_helper tt.

(** A tactic to eliminate equalities in the context. *)
Ltac ElimEq := repeat match goal with [H : _ = _|- _] => destruct H end.

Hint Extern 1 => progress ElimEq : core.

(** A tactic to simplify terms before rewriting them. *)

Ltac cbn_rewrite W :=
  let H := fresh "H" in set (H := W); cbn in H; rewrite H; clear H.

Ltac cbn_rewrite_in W V :=
  let H := fresh "H" in set (H := W); cbn in H; rewrite H in V; clear H.

Ltac cbn_rewrite_back W :=
  let H := fresh "H" in set (H := W); cbn in H; rewrite <- H; clear H.

Ltac cbn_rewrite_back_in W V :=
  let H := fresh "H" in set (H := W); cbn in H; rewrite <- H in V; clear H.

Tactic Notation "cbn_rewrite" constr(W) := cbn_rewrite W.
Tactic Notation "cbn_rewrite" constr(W) "in" hyp_list(V) := cbn_rewrite_in W V.
Tactic Notation "cbn_rewrite" "<-" constr(W) := cbn_rewrite_back W.
Tactic Notation "cbn_rewrite" "<-" constr(W) "in" hyp_list(V) :=
  cbn_rewrite_back_in W V.

(** Equality on sigma type under proof irrelevance *)

Lemma sig_proof_irrelevance {A : Type} (P : A → Prop) (X Y : sig P) :
  proj1_sig X = proj1_sig Y → X = Y.
Proof.
  basic_simpl; ElimEq; PIR; trivial.
Qed.

Hint Extern 2 (exist ?A _ _ = exist ?A _ _) =>
  apply sig_proof_irrelevance : core.

(* Automating use of functional_extensionality *)
Ltac FunExt :=
progress (
    repeat (
        match goal with
          [|- _ = _] =>
          let x := fresh "x" in
          extensionality x
        end
      )
  )
.

Hint Extern 1 => FunExt : core.

Lemma pair_eq (A B : Type) (a b : A * B) : fst a = fst b → snd a = snd b → a = b.
Proof.
  intros H1 H2.
  destruct a; destruct b.
  cbn in *.
  repeat match goal with [H : _ = _|-_] => destruct H end.
  trivial.
Qed.

Hint Resolve pair_eq : core.

Definition transport {A B : Type} (eq : A = B) (x : A) : B :=
  match eq in _ = T return T with eq_refl => x end.

Arguments transport : simpl never.

Lemma transport_refl {A} (eq : A = A) (x : A) : transport eq x = x.
Proof. replace eq with (eq_refl A); [done|apply proof_irrelevance]. Qed.

Lemma transport_trans {A B C} (eqAB : A = B) (eqBC : B  = C) (x : A) : transport eqBC (transport eqAB x) = transport (eq_trans eqAB eqBC) x.
Proof. destruct eqAB; destruct eqBC; done. Qed.

(** Tactics to apply a tactic to all hypothesis in an efficient way.
This is due to Jonathan's (jonikelee@gmail.com) message on coq-club *)

Ltac revert_clearbody_all :=
 repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac hyp_stack :=
 constr:(ltac:(revert_clearbody_all;constructor) : True).

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
