Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Basic_Cons.CCC.
Require Import PreSheaf.PreSheaf.
Require Export PreSheaf.Terminal.
Require Export PreSheaf.Product.
Require Export PreSheaf.Exponential.

(** Category of presheaves over C is cartesian closed. *)
Program Instance PShCat_CCC (C : Category) : CCC (PShCat C)
  :=
    {|
      CCC_term := PSh_Terminal C;
      CCC_HP := PSh_Has_Products C;
      CCC_HEXP := PSh_Has_Exponentials C
    |}.


