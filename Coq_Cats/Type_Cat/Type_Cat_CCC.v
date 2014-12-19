Require Import Category.Main.
Require Import Basic_Cons.CCC.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := program_simpl; auto 3.

Program Instance unit_Type_term : Terminal Type_Cat :=
{
  terminal := unit;
  t_morph := λ _ _, tt
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  destruct (f x); destruct (g x); reflexivity.
Qed.

Program Instance prod_Product (A B : Type) : Product A B :=
{
  product := (A * B)%type
}.

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  apply (fun p => equal_f p x) in H1; apply (fun p => equal_f p x) in H2.
  simpl in H1, H2.
  destruct (f x); destruct (g x); simpl in *; subst; trivial.
Qed.

Program Instance Type_Cat_Has_Products : Has_Products Type_Cat.

Program Instance fun_exp (A B : Type) : Exponential A B :=
{
  exponential := A -> B
}.

Next Obligation. (* Exp_morph_com *)
Proof.
  extensionality x; destruct x; reflexivity.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
  extensionality a; extensionality x.
  apply (fun p => equal_f p (a, x)) in H0.
  simpl in H0; trivial.
Qed.

(* fun_exp defined *)

Program Instance Type_Cat_Has_Exponentials : Has_Exponentials Type_Cat.

(* Category of Types is cartesian closed *)

Program Instance Type_Cat_CCC : CCC Type_Cat.


