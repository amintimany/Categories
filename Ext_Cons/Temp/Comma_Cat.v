Require Import Category.Main.
Require Export Ext_Cons.Arrow.
Require Import Functor.Functor.


Set Primitive Projections.

Set Universe Polymorphism.


Section Comma_Cat.
  Context (B C D : Category) (F : Functor B C) (G : Functor D C).

  Class Comma_Obj : Type :=
    {
      CMO_Obj1 : B;
      CMO_Obj2 : D;
      CMO_Hom : Hom (F _o CMO_Obj1) (G _o CMO_Obj2)
    }.

  Program Instance Arrow_of_Comma_Obj (cmo : Comma_Obj) : Arrow C :=
    {
      Arr := @CMO_Hom cmo
    }.

  Coercion Arrow_of_Comma_Obj : Comma_Obj >-> Arrow.

  Program Instance Comma_Cat : Category :=
    {
      Obj := Comma_Obj;

      Hom := (@Arrow_Hom C);

      compose := λ _ _ _ f g, Arrow_Hom_compose _ f g;
      
      id := λ a, Arrow_id _
    }.

  (* Arrow_Cat defined *)

End Comma_Cat.
