Require Import Category.Main.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

(** The empty type is the initial object of category of types. *)
Program Instance Empty_init : Initial Type_Cat := {|terminal := (Empty : Type)|}.
