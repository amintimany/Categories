Require Import Category.Main.
Require Import Categories.Monoid_Cat.
Require Import Coq.Lists.List.

Section List_Monoid_Cat.
  Context (A : Type).
  
  Hint Resolve app_assoc app_nil_r.

  Program Instance List_Monoid : Monoid :=
    {
      Mon_car := list A;
      
      Mon_op := λ a b, (a ++ b)%list;
      
      Mon_unit := nil
    }.

  Definition List_Monoid_Cat := Monoid_Cat List_Monoid.

End List_Monoid_Cat.
