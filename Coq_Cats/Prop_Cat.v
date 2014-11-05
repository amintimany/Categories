Require Import Category.Main.
Require Import Basic_Cons.CCC.
Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Sum.

Set Primitive Projections.

Set Universe Polymorphism.

(*
**********************************************************
***************                          *****************
***************     Prop Category        *****************
***************                          *****************
**********************************************************
*)


(* The category of Types in Coq's "Prop" universe (Coq's Proposits) *)

Program Instance Prop_Cat : Category Prop (λ A B, A → B) :=
{
  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x

}.

Program Instance False_init : Initial Prop_Cat False.

Next Obligation. (* i_morph *)
Proof.
  contradiction.
Qed.

Next Obligation. (* i_morph_unique *)
Proof.
  extensionality x; contradiction.
Qed.

(* Prop_init Proved! *)

Program Instance Prop_Cat_Has_Init : Has_Initial Prop_Cat.


Program Instance True_term : Terminal Prop_Cat True.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x; destruct (f x); destruct (g x); reflexivity.
Qed.

(* Prop_term Proved! -- t_morph is proven by Program system :-) it could prove for us that from any premise we can conclude True! :-) *)

Program Instance Prop_Cat_Has_Term : Has_Terminal Prop_Cat.

Program Instance Conj_Product (P Q : Prop) : Product Prop_Cat P Q (P /\ Q).

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  apply (fun p => equal_f p x) in H1; apply (fun p => equal_f p x) in H2.
  simpl in H1, H2.
  destruct (f x); destruct (g x); simpl in *; subst; trivial.
Qed.

(* Prop_Product is proven -- the rest of the obligations (e.g., projections, etc.) are defined and proven by Program system :-) *)

Program Instance Prop_Cat_Has_Products : Has_Products Prop_Cat.

Program Instance implication_exp (P Q : Prop) : Exponential Prop_Cat Prop_Cat_Has_Products P Q (P -> Q).

Next Obligation. (* Exp_morph_com *)
Proof.
  extensionality a; destruct a; reflexivity.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
  extensionality a; extensionality x.
  apply (fun p => equal_f p (conj a x)) in H0.
  simpl in H0; trivial.
Qed.

(* Category of Prop Universe is cartesian closed *)

Program Instance Prop_Cat_Has_Exponentials : Has_Exponentials Prop_Cat.

Program Instance Prop_Cat_CCC : CCC Prop_Cat.


Program Instance Disj_Sum (P Q : Prop) : Sum Prop_Cat P Q (P \/ Q).

Next Obligation. (* Sum_morph_ex *)
Proof.
  tauto.
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

(* Prop_Sum is proven -- the rest of the obligations (e.g., injections, etc.) are proven by Program system :-) *)

Program Instance Prop_Cat_Has_Sums : Has_Sums Prop_Cat.





