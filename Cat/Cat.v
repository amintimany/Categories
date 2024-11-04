From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.

(** Cat, the category of (small) categories, is a category whose objects are
    (small) categories and morphisms are functors.

In this development, the (relative) smallness/largeness is represented by
universe levels and universe polymorphism of Coq.
*)
Definition Cat : category :=
{|
  obj := category;

  hom := functor;

  compose := fun C D E => functor_compose;

  assoc := fun C D E F (G : functor C D) (H : functor D E) (I : functor E F) =>
            @Functor_assoc _ _ _ _ G H I;

  assoc_sym := fun C D E F (G : functor C D) (H : functor D E) (I : functor E F) =>
            eq_sym (@Functor_assoc _ _ _ _ G H I);

  id := fun C => functor_id C;

  left_id := fun C D => @Functor_id_unit_left C D;

  right_id := fun C D => @Functor_id_unit_right C D
|}.
