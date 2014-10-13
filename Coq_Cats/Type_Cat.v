Require Import Category.Core.
Require Import Basic_Cons.CCC.
Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Sum.
Require Export Essentials.Empty.

Local Obligation Tactic := program_simpl; auto 3.

(* The category of Coq Types! *)

(*
**********************************************************
***************                          *****************
***************     Type Category        *****************
***************                          *****************
**********************************************************
*)

(* The category of Types (Coq's "Type")*)

Program Instance Type_Cat : Category Type (λ A B, A → B):=
{
  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x

}.

Program Instance Empty_init : Initial Type_Cat Empty.

(* Empty_init Proved! *)

Program Instance Type_Cat_Has_Initial : Has_Initial Type_Cat :=
{
  HI_init := Empty
}.

(* Type_Cat_Has_Initial Proved! *)


Program Instance Singleton_Type_term : Terminal Type_Cat unit :=
{
  t_morph := λ _ _, tt
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  destruct (f x); destruct (g x); reflexivity.
Qed.

(* Singleton_Type_term Proved! *)

Program Instance Type_Cat_Has_Terminal : Has_Terminal Type_Cat :=
{
  HT_term := unit
}.

(* Type_Cat_Has_Terminal Proved! *)

Program Instance prod_Product (A B : Type) : Product Type_Cat A B (A * B)%type.

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  apply (fun p => equal_f p x) in H1; apply (fun p => equal_f p x) in H2.
  simpl in H1, H2.
  destruct (f x); destruct (g x); simpl in *; subst; trivial.
Qed.

Program Instance Type_Cat_Has_Products : Has_Products Type_Cat :=
{
  HP_prod := fun A B => (A * B)%type;
  HP_prod_prod := prod_Product
}.


Program Instance fun_exp (A B : Type) : Exponential Type_Cat Type_Cat_Has_Products A B (A -> B).

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

Program Instance sum_Sum (A B : Type) : Sum Type_Cat A B (A + B)%type.

Next Obligation. (* Sum_morph_ex *)
Proof.
  exact (
      match X with
        | inl a => r1 a
        | inr b => r2 b
      end
    ).
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

(* sum_Sum proved! -- the rest of the obligations (i.e., sum_morph omposed with injections commuting with injections of arbitrary objects with two injections ) are proven by Program system :-) *)

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat.


