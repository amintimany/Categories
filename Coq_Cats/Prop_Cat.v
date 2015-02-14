Require Import Category.Main.
Require Import Basic_Cons.CCC.

(*
**********************************************************
***************                          *****************
***************     Prop Category        *****************
***************                          *****************
**********************************************************
*)


(* The category of Types in Coq's "Prop" universe (Coq's Proposits) *)

Program Instance Prop_Cat : Category :=
{
  Obj := Prop; 

  Hom := (λ A B, A → B);

  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x
}.

Local Hint Extern 1 => contradiction.

Program Instance False_init : Initial Prop_Cat := {|terminal := False|}.

Local Hint Extern 1 => match goal with |- ?A = ?B :> True => destruct A; destruct B end.

Program Instance True_term : Terminal Prop_Cat := {terminal := True}.

Local Hint Extern 1 => match goal with |- ?A = ?B :> _ ∧ _ => destruct A; destruct B end.

Program Instance Conj_Product (P Q : Prop) : Product P Q := {product := (P ∧ Q)}.

Next Obligation. (* Prod_morph_unique *)
Proof.
  extensionality x.
  apply (fun p => equal_f p x) in H1; apply (fun p => equal_f p x) in H2.
  simpl in H1, H2.
  destruct (f x); destruct (g x); cbn in *; subst; trivial.
Qed.

Program Instance Prop_Cat_Has_Products : Has_Products Prop_Cat := fun _ _ => _.

Local Hint Extern 1 => match goal with H : _ ∧ _ |- _ => destruct H end.

Program Instance implication_exp (P Q : Prop) : Exponential P Q := {exponential := (P -> Q)}.

Next Obligation. (* Exp_morph_unique *)
Proof.
  extensionality a; extensionality x.
  apply (fun p => equal_f p (conj a x)) in H0.
  trivial.
Qed.

(* Category of Prop Universe is cartesian closed *)

Program Instance Prop_Cat_Has_Exponentials : Has_Exponentials Prop_Cat := fun _ _ => _.

Program Instance Prop_Cat_CCC : CCC Prop_Cat.

Local Hint Extern 1 => tauto.

Local Hint Extern 1 => match goal with H : _ ∨ _ |- _ => destruct H end.

Program Instance Disj_Sum (P Q : Prop) : Sum P Q := {|product := (P ∨ Q)|}.

Next Obligation. (* Sum_morph_unique *)
Proof.
  extensionality x.
  destruct x as [x1|x2].
  + apply (fun p => equal_f p x1) in H1; auto.
  + apply (fun p => equal_f p x2) in H2; auto.
Qed.

(* Prop_Sum is proven -- the rest of the obligations (e.g., injections, etc.) are proven by Program system :-) *)

Program Instance Prop_Cat_Has_Sums : Has_Sums Prop_Cat := fun _ _ => _.





