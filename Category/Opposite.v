From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category.

(** The oposite of a category C is a category with the same objects where the arrows are inverted. 
As a result, f ∘_Cᵒᵖ g is just g ∘_C f and consequently, assoc is assoc_sym (reversed with arrow
arguments) and vice versa. Similarly, id_unit_left and id_unit_right are also swapped. *)

Definition opposite (C : category) : category :=
{|

  obj := obj C;

  hom := fun a b => (hom b a)%morphism;

  compose :=
    fun a b c (f : hom b a) (g : hom c b) => compose g f;

  id := fun c => id C c;

  assoc := fun _ _ _ _ f g h => assoc_sym h g f;

  assoc_sym := fun _ _ _ _ f g h => assoc h g f;

  left_id := fun _ _ h => @right_id C _ _ h;

  right_id := fun _ _ h => @left_id C _ _ h

|}.

Notation "C 'ᴼᴾ'" := (opposite C) : category_scope.
