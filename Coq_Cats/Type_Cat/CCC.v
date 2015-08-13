Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Basic_Cons.CCC.
Require Import Coq_Cats.Type_Cat.Type_Cat.

(* Local Obligation Tactic := basic_simpl; auto. *)

(* if we use (unit : set) as terminal object then the level of arrows in Type_Cat
is brought down to set which cuases problems in working with Type_Cat, e.g.,
for showing Type_Cat has a subobject classifier. 
*)

(*
Program Instance unit_Type_term : Terminal Type_Cat :=
{
  terminal := unit;
  t_morph := fun _ _=> tt
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  destruct (f x); destruct (g x); reflexivity.
Qed.
 *)

Parameter UNIT : Type.

Parameter TT : UNIT.

Axiom UNIT_SINGLETON : ∀ x y : UNIT, x = y.

(** The type unit in coq is the terminal object of category of types. *)
Program Instance unit_Type_term : Terminal Type_Cat :=
{
  terminal := UNIT;
  t_morph := fun _ _ => TT
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  apply UNIT_SINGLETON.
Qed.

(** The cartesian product of types is the categorical notion of products in category of types. *)
Program Definition prod_Product (A B : Type) : @Product Type_Cat A B :=
{|
  product := (A * B)%type;
  Pi_1 := fst;
  Pi_2 := snd;
  Prod_morph_ex := fun p x y z => (x z, y z)
|}.

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  repeat
    match goal with
      [H : _ = _ |- _] =>
      apply (fun p => equal_f p x) in H
    end.
  basic_simpl.  
  destruct (f x); destruct (g x); cbn in *; subst; trivial.
Qed.

Program Instance Type_Cat_Has_Products : Has_Products Type_Cat := prod_Product.

(** The function type in coq is the categorical exponential in the category of types. *)
Program Definition fun_exp (A B : Type) : @Exponential Type_Cat _ A B :=
{|
  exponential := A -> B;
  eval := fun x => (fst x) (snd x);
  Exp_morph_ex := fun h z u v=>  z (u, v)
|}.

Next Obligation. (* Exp_morph_unique *)
Proof.
  extensionality a; extensionality x.
  repeat
    match goal with
      [H : _ = _ |- _] =>
      apply (fun p => equal_f p (a, x)) in H
    end.
  transitivity (f (a, x)); auto.
Qed.

(* fun_exp defined *)

Program Instance Type_Cat_Has_Exponentials : Has_Exponentials Type_Cat := fun_exp.

(* Category of Types is cartesian closed *)

Program Instance Type_Cat_CCC : CCC Type_Cat.


