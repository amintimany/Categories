Require Import Category.Main.
Require Export Essentials.Empty.

(*
**********************************************************
***************                          *****************
***************      Set Category        *****************
***************                          *****************
**********************************************************
*)


(* The category of types in Set universe (Coq's "Set")*)

Program Instance Set_Cat : Category :=
{
  Obj := Set;

  Hom := (λ A B, A → B);

  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x
}.

