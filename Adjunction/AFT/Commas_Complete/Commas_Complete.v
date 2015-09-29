Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import
        Limits.Limit
        Limits.GenProd_GenSum
        Limits.GenProd_Eq_Limits
.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.Main.
Require Import Ext_Cons.Comma.

Require Import Archetypal.Discr.Discr.

Require Import
        Adjunction.AFT.Commas_Complete.Commas_GenProd
        Adjunction.AFT.Commas_Complete.Commas_Equalizer
.

(** We show that if C is a complete category and G : C –≻ D preserves limits,
then every comma category (Comma (Func_From_SingletonCat x) G) for (x : D) is
complete. *)
Section Commas_Complete.
  Context
    {C D : Category}
    {CC : Complete C}
    {G : (C –≻ D)%functor}
    (GCont : Continuous CC G)
    (x : D)
  .

  Definition Commas_Complete : Complete (Comma (Func_From_SingletonCat x) G)
    :=
      @GenProd_Eq_Complete
        (Comma (Func_From_SingletonCat x) G)
        (@Comma_GenProd _ _ _ _ GCont x)
        (@Comma_Equalizer _ _ _ _ GCont x)
  .

End Commas_Complete.
