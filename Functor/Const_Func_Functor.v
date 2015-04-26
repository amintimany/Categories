Require Import Category.Main.
Require Import Functor.Functor Functor.Const_Func.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.

Section Const_Func_Functor.
  Context (C D : Category).

  Program Instance Const_Func_Functor : Functor C (Func_Cat D C) :=
    {
      FO := fun c => Const_Func D c;
      FA := fun _ _ h => {|Trans := fun c => h|}
    }.

End Const_Func_Functor.