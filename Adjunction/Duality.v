Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.NatTrans NatTrans.NatIso.
Require Import Adjunction.Adjunction.

Section Hom_Adj_Duality.
  Context {C D : Category} {F : Functor C D} {G : Functor D C} (adj : Hom_Adjunct F G).
  
  Instance Hom_Adjunct_Duality : Hom_Adjunct (Opposite_Functor G) (Opposite_Functor F) := (Prod_Func_Hom_Func (Inverse_Isomorphism adj)).

End Hom_Adj_Duality.

Section Adj_Duality.
  Context {C D : Category} {F : Functor C D} {G : Functor D C} (adj : Adjunct F G).
  
  Instance Adjunct_Duality : Adjunct (Opposite_Functor G) (Opposite_Functor F) := (Hom_Adj_to_Adj (Hom_Adjunct_Duality (Adj_to_Hom_Adj adj))).

End Adj_Duality.