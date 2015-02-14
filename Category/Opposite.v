Require Import Category.Category.

(* Oposite Category *)

Instance Opposite (C : Category) : Category :=
{

  Obj := @Obj C;
           
  Hom := λ a b, Hom C b a;

  compose := λ a b c (f : Hom b a) (g : Hom c b), @compose C c b a g f;

  id := λ c, @id C c;
  
  assoc := λ _ _ _ _ f g h, @assoc_sym C _ _ _ _ h g f;

  assoc_sym := λ _ _ _ _ f g h, @assoc C _ _ _ _ h g f;

  id_unit_left := λ _ _ h, @id_unit_right C _ _ h;
  
  id_unit_right := λ _ _ h, @id_unit_left C _ _ h
                   
}.

(* Oposite defined *)

Notation "C '^op'" := (Opposite C) (at level 9, no associativity).

