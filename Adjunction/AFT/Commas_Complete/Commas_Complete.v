From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories.Limits Require Import Limit GenProd_GenSum GenProd_Eq_Limits.
From Categories.Functor Require Import Functor Const_Func Functor_Ops.
From Categories Require Import NatTrans.Main.
From Categories Require Import Ext_Cons.Comma.

From Categories Require Import Archetypal.Discr.Discr.

From Categories.Adjunction.AFT.Commas_Complete Require Import
     Commas_GenProd Commas_Equalizer.

(** We show that if C is a complete category and G : C –≻ D preserves limits,
then every comma category (Comma (Func_From_SingletonCat x) G) for (x : D) is
complete. *)
Section Commas_Complete.
  Context
    {C D : Category}
    {CC : Complete C}
    {G : (C --> D)%functor}
    (GCont : Continuous CC G)
    (x : D).

  Definition Commas_Complete : Complete (Comma (Const_Func 1 x) G)
    :=
      @GenProd_Eq_Complete
        (Comma (Const_Func 1 x) G)
        (@Comma_GenProd _ _ _ _ GCont x)
        (@Comma_Equalizer _ _ _ _ GCont x).

End Commas_Complete.
