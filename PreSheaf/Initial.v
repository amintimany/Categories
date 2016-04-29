Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Basic_Cons.Terminal.
Require Import PreSheaf.PreSheaf.

Section Initial.
  Context (C : Category).
  
  (** The initial element of the category of presheaves. *)
  Program Definition PSh_Init_Func : Functor (C^op) Type_Cat :=
    {|
      FO := fun _ => (Empty : Type)
    |}.

  Local Hint Resolve NatTrans_eq_simplify.
  Local Hint Extern 1 => progress cbn in *.

  (** The functor that maps to the empty type in coq is the terminal object of
      presheaves. *)
  Program Instance PSh_Initial : (𝟘_ (PShCat C))%object :=
    {|
      terminal := PSh_Init_Func;
      t_morph := fun u => {|Trans := fun x y => _ |}
    |}.
    
End Initial.
