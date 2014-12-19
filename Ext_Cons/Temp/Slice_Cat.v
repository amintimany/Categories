Require Import Category.Category.
Require Import Functor.Functor Functor.Functor_Ops Const_Func.
Require Import Ext_Cons.Comma.
Require Import Categories.Discr.

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

  Instance Slice_Cat : Category := Comma C C 1 Functor_id (Const_Func _ c).

End Slice_Cat.
