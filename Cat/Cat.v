Require Import Category.Main.
Require Import Functor.Main.

Record CAT : Type :=
  mkCAT {
      OBJECTS : Type;
      HOMS : OBJECTS → OBJECTS → Type;
      THE_CAT : Category OBJECTS HOMS
    }.

Coercion THE_CAT : CAT >-> Category.

Coercion mkCAT : Category >-> CAT.

Instance Cat : Category CAT (λ A B, Functor A B) :=
{
  compose := fun C D E => Functor_compose;
  
  assoc := fun (C D E F : CAT) (G : Functor C D) (H : Functor D E) (I : Functor E F) =>
            @Functor_assoc _ _ _ _ _ _ _ _ _ _ _ _ G H I;

  assoc_sym := fun (C D E F : CAT) (G : Functor C D) (H : Functor D E) (I : Functor E F) =>
            eq_sym (@Functor_assoc _ _ _ _ _ _ _ _ _ _ _ _ G H I);

  id := fun (C : CAT) => Functor_id;

  id_unit_left := fun (C D : CAT) => @Functor_id_unit_left _ _ _ _ _ _;

  id_unit_right := fun (C D : CAT) => @Functor_id_unit_right _ _ _ _ _ _
}.



