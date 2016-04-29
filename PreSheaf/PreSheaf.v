Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.

(** A presheaf on C is a functor Cᵒᵖ –≻ Type_Cat. *)
Definition PreSheaf (C : Category) := Functor (C^op) Type_Cat.

(** The category of presheaves. *)
Definition PShCat (C : Category) := Func_Cat (C^op) Type_Cat.