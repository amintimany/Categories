Require Import Category.Main.
Require Import Basic_Cons.Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 2.

Program Instance sum_Sum (A B : Type) : Sum A B :=
{|
  product := (A + B)%type
|}.

Next Obligation. (* Sum_morph_ex *)
Proof.
  match goal with
      [X : (A + B)%type |- _] =>
      refine (
          match X with
            | inl a => _ a
            | inr b => _ b
          end
        ); auto 1
  end.
Defined.

Next Obligation. (* Sum_morph_unique *)
Proof.
  extensionality x.
  destruct x;
    match goal with
        [|- f (?m ?y) = g (?m ?y)] =>
        apply (@equal_f _ _ (fun x => f (m x)) (fun x => g (m x)))
    end; auto.
Qed.

(* sum_Sum defined *)

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat := fun _ _ => _.


