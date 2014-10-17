Require Import Category.Main.
Require Import Basic_Cons.Sum.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 2.

Program Instance sum_Sum (A B : Type) : Sum Type_Cat A B (A + B)%type.

Next Obligation. (* Sum_morph_ex *)
Proof.
  refine (
      match X with
        | inl a => _ a
        | inr b => _ b
      end
    ); auto 1.
Defined.

Next Obligation. (* Sum_morph_unique *)
Proof.
  extensionality x.
  destruct x as [x1 | x2].
  {
    apply (fun p => equal_f p x1) in H1.
    cbv in H1; auto.
  }
  {
    apply (fun p => equal_f p x2) in H2.
    cbv in H2; auto.
  }
Qed.

(* sum_Sum defined *)

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat.


