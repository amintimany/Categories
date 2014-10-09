Require Import Category.Core.
Require Import Basic_Cons.Core.
Require Export Essentials.Empty.


(*
**********************************************************
***************                          *****************
***************      Set Category        *****************
***************                          *****************
**********************************************************
*)


(* The category of types in Set universe (Coq's "Set")*)

Program Instance Set_Cat : Category Set (λ A B, A → B) :=
{

  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x

}.

