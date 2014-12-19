Require Import Category.Main.
Require Export Basic_Cons.Terminal.
Require Export Basic_Cons.Product.
Require Export Basic_Cons.Exponential.

Set Primitive Projections.

Set Universe Polymorphism.

(* Cartesian Closed Category : one that has terminal element, binary products (all finite products) and exponential *)
Class CCC (C : Category) : Type :=
{
  CCC_term : Terminal C;
  CCC_HC : Has_Products C;
  CCC_HE : Has_Exponentials C
}.

Existing Instances CCC_term CCC_HC CCC_HE.


