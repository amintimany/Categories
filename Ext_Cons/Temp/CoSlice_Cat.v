Require Import Category.Main.
Require Export Ext_Cons.Arrow_From.

Set Primitive Projections.

Set Universe Polymorphism.

(*
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, an arrow from g to h is a pair of arrows f : a → b s.t. the ollowing commutes:

            g
         c ←––– a
         ↑     /
         ∣    /
        h∣   / f
         |  /
         | ↙
         b 

*)

Section CoSlice_Cat.
  Context (C : Category) (c : Obj).

  Program Instance CoSlice_Cat : Category :=
    {
      Obj := Arrow_From C c;

      Hom := @Arrow_From_Hom C c;

      compose := λ _ _ _ f g, Arrow_From_Hom_compose _ f g;
      
      id := λ a, Arrow_From_id _
    }.

  (* Arrow_Cat defined *)

End CoSlice_Cat.
