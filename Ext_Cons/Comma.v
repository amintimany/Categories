Require Import Category.Category.
Require Import Ext_Cons.Arrow.
Require Import Functor.Functor Functor.Functor_Ops Const_Func.
Require Import Categories.Discr.

Set Primitive Projections.

Set Universe Polymorphism.

Section Comma.
  Context (B C D : Category) (F : Functor B C) (G : Functor D C).

  Class Comma_Obj : Type :=
    {
      CMO_src : B;
      CMO_trg : D;
      CMO_hom : Hom (F _o CMO_src) (G _o CMO_trg)
    }.

  Program Instance Arrow_of_Comma_Obj (cmo : Comma_Obj) : Arrow C :=
    {
      Arr := CMO_hom
    }.

  Coercion Arrow_of_Comma_Obj : Comma_Obj >-> Arrow.

  Program Instance Comma : Category :=
    {
      Obj := Comma_Obj;

      Hom := (@Arrow_Hom C);

      compose := λ _ _ _ f g, Arrow_Hom_compose _ f g;

      id := λ a, Arrow_id _
    }.

End Comma.

Section Slice_CoSlice.
  Context (C : Category) (c : Obj).
  
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

  Instance Slice : Category := Comma C C 1 Functor_id (Const_Func _ c).

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

  Instance CoSlice : Category := Comma 1 C C (Const_Func _ c) Functor_id.

End Slice_CoSlice.

Section Arrow_Cat.
  Context (C : Category).

  (*
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: for g : a → b and h : c → d, an arrow from g to h is a pair of arrows (f,f') s.t. the ollowing commutes:

             g
         a ––––→ b
         ∣       ∣
        f∣       ∣f'
         ↓       ↓
         c –——–→ d
             h
   *)

  Instance Arrow_Cat : Category := Comma C C C Functor_id Functor_id.

End Arrow_Cat.


