Require Import Category.Main.
Require Import Ext_Cons.Arrow_To.


Set Primitive Projections.

Set Universe Polymorphism.

(*
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, an arrow from g to h is a pair of arrows f : a → b s.t. the ollowing commutes:

           g
         a –––→ c
         |     ↗
         ∣    /    
        f∣   / h
         |  /
         ↓ /
         b 

*)

Section Slice_Cat.
  Context (C : Category) (c : Obj).

  Program Instance Slice_Cat : Category :=
    {
      Obj := (Arrow_To C c);

      Hom := (@Arrow_To_Hom C c);

      compose := λ _ _ _ f g, Arrow_To_Hom_compose _ f g;
      
      id := λ a, Arrow_To_id _
    }.

  (* Arrow_Cat defined *)

End Slice_Cat.
