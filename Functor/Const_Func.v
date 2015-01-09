Require Import Category.Main.
Require Import Functor.Functor.

Section Const_Func.
  Context (C : Category) {D : Category} (a : @Obj D).

  Program Instance Const_Func : Functor C D :=
    {
      FO := fun _ => a;
      FA := fun _ _ _ => id a
    }.

End Const_Func.