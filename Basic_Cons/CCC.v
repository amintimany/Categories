Require Import Category.Main.
Require Export Basic_Cons.Terminal.
Require Export Basic_Cons.Product.
Require Export Basic_Cons.Exponential.

(* Cartesian Closed Category : one that has terminal element, binary products (all finite products) and exponential *)
Class CCC `(C : Category Obj) : Type :=
{
  CCC_HT : Has_Terminal C;
  CCC_HC : Has_Products C;
  CCC_HE : Has_Exponentials C
}.

Existing Instances CCC_HT CCC_HC CCC_HE.


