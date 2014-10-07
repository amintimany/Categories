Require Import Category.Core.

Class Monoid : Type :=
{
  Mon_car : Type;
  
  Mon_op : Mon_car → Mon_car → Mon_car;

  Mon_assoc : ∀ a b c, Mon_op a (Mon_op b c) = Mon_op (Mon_op a b) c;

  Mon_unit : Mon_car;

  Mon_unit_left : ∀ a, Mon_op Mon_unit a = a;

  Mon_unit_right : ∀ a, Mon_op a Mon_unit = a
}.

Section Monoid_Cat.
  Context (M : Monoid).

  Hint Resolve Mon_unit_left Mon_unit_right Mon_assoc.

  Program Instance Monoid_Cat : Category unit (λ _ _, @Mon_car M) :=
    {
      compose := λ _ _ _, @Mon_op M;
      id := λ a, Mon_unit
    }.

End Monoid_Cat.