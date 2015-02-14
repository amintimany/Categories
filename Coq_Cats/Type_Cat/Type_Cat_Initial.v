Require Import Category.Main.
Require Import Basic_Cons.Terminal.
Require Import Essentials.Empty.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

Program Instance Empty_init : Initial Type_Cat := {|terminal := Empty|}.

(* Empty_init Proved! *)


