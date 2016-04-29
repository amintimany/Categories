Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

(** The empty type is the initial object of category of types. *)
Program Instance Empty_init : (𝟘_ Type_Cat)%object :=
  {|terminal := (Empty : Type)|}.
