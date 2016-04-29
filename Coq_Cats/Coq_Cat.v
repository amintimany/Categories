Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.

(** The general form a category whose objects are types (in some universe) and
     arrows are functions among them. *)

Notation Coq_Cat U :=
{|
  Obj := U;

  Hom := (fun A B => A → B);

  compose := fun A B C (g : A → B) (h : B → C) => fun (x : A) => h (g x);

  id := fun A => fun x => x
|}.

