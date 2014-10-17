Require Import Category.Main.
Require Import Ext_Cons.Arrow_To.

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
  Context `(C : Category Obj Hom) (c : Obj).

  Program Instance Slice_Cat : Category (Arrow_To C c) (@Arrow_To_Hom _ _ C c) :=
    {
      compose := λ _ _ _ f g, Arrow_To_Hom_compose _ f g;
      
      id := λ a, Arrow_To_id _
    }.

  (* Arrow_Cat defined *)

End Slice_Cat.
