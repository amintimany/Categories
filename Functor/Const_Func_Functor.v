Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Functor Functor.Const_Func.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.

(** The functor that maps each object c in C to the 
    constant functor that maps each object of D to c in Func_Cat D C. *)
Section Const_Func_Functor.
  Context (C D : Category).

  Program Definition Const_Func_Functor : (C –≻ (Func_Cat D C))%functor :=
    {|
      FO := fun c => Const_Func D c;
      FA := fun _ _ h => {|Trans := fun c => h|}
    |}.

End Const_Func_Functor.