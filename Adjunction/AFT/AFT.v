Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Ext_Cons.Comma.
Require Import Limits.Limit.
Require Import Archetypal.Discr.Discr.
Require Import
        Adjunction.Adjunction
        Adjunction.Univ_Morph
.
Require Import
        Adjunction.AFT.Solution_Set_Cond
        Adjunction.AFT.Commas_Complete.Commas_Complete
.

Section AFT.
  Local Open Scope functor_scope.

  Context
    {C D : Category}
    {CC : Complete C}
    {G : C –≻ D}
    (GCont : Continuous CC G)
    (SSC : ∀ x, Solution_Set_Cond (Comma (Func_From_SingletonCat x) G))
  .
  
  Program Definition Adjoint_Functor_Theorem : _ ⊣ G :=
    Universal_Morphism_Right_Adjonit
      G
      (fun x : D => Complete_SSC_Initial (Commas_Complete GCont x) (SSC x))
  .

End AFT.