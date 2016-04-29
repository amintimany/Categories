Require Import Essentials.Notations.
Require Import Category.Main.
Require Export Basic_Cons.Terminal.
Require Export Basic_Cons.Product.
Require Export Basic_Cons.Exponential.
Require Export Basic_Cons.Exponential_Functor.

(** Cartesian Closed Category : one that has terminal element, binary products
    (all finite products) and exponential *)
Class CCC (C : Category) : Type :=
{
  CCC_term : (𝟙_ C)%object;
  CCC_HP : Has_Products C;
  CCC_HEXP : Has_Exponentials C
}.

Arguments CCC_term _ {_}, {_ _}.
Arguments CCC_HP _ {_} _ _, {_ _} _ _.
Arguments CCC_HEXP _ {_} _ _, {_ _} _ _.

Existing Instances CCC_term CCC_HP CCC_HEXP.


