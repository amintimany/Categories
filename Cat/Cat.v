Require Import Category.Core.
Require Import Functor.Core.


Record CAT : Type :=
  mkCAT {
      OBJECTS : Type;
      HOMS : OBJECTS → OBJECTS → Type;
      THE_CAT : Category OBJECTS HOMS
    }.

Definition F_CAT (C C' : CAT) := Functor (THE_CAT C) (THE_CAT C').

Instance Cat : Category CAT F_CAT :=
{
  compose := fun C D E =>
              @Functor_compose
                _ _ (THE_CAT C)
                _ _ (THE_CAT D)
                _ _ (THE_CAT E);
  
  assoc := fun (C D E F : CAT) (G : F_CAT C D) (H : F_CAT D E) (I : F_CAT E F) =>
            @Functor_assoc
              _ _ (THE_CAT C)
              _ _ (THE_CAT D)
              _ _ (THE_CAT E)
              _ _ (THE_CAT F)
              G H I;
  assoc_sym := fun (C D E F : CAT) (G : F_CAT C D) (H : F_CAT D E) (I : F_CAT E F) =>
            eq_sym (@Functor_assoc
              _ _ (THE_CAT C)
              _ _ (THE_CAT D)
              _ _ (THE_CAT E)
              _ _ (THE_CAT F)
              G H I);

  id := fun (C : CAT) =>
         @Functor_id
          _ _ (THE_CAT C);

  id_unit_left := fun (C D : CAT) =>
                   @Functor_id_unit_left
                     _ _ (THE_CAT C)
                     _ _ (THE_CAT D);

  id_unit_right := fun (C D : CAT) =>
                   @Functor_id_unit_right
                     _ _ (THE_CAT C)
                     _ _ (THE_CAT D)
}.



