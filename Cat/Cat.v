Require Import Category.Main.
Require Import Functor.Main.

Set Universe Polymorphism.

Instance Cat : Category :=
{
  Obj := Category;

  Hom := Functor;

  compose := fun C D E => Functor_compose;
  
  assoc := fun C D E F (G : Functor C D) (H : Functor D E) (I : Functor E F) =>
            @Functor_assoc _ _ _ _ G H I;

  assoc_sym := fun C D E F (G : Functor C D) (H : Functor D E) (I : Functor E F) =>
            eq_sym (@Functor_assoc _ _ _ _ G H I);

  id := fun C => Functor_id;

  id_unit_left := fun C D => @Functor_id_unit_left _ _;

  id_unit_right := fun C D => @Functor_id_unit_right _ _
           
}.