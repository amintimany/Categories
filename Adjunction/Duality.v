Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.NatTrans NatTrans.NatIso.
Require Import Adjunction.Adjunction.

Section Hom_Adj_Duality.
  Context {C D : Category} {F : Functor C D} {G : Functor D C} (adj : (F ⊣_hom G)%functor).

  (** Duality for hom adjunctions. *)
  Definition Hom_Adjunct_Duality : (G^op ⊣_hom F^op)%functor := (Prod_Func_Hom_Func (Inverse_Isomorphism adj)).

End Hom_Adj_Duality.

Section Adj_Duality.
  Context {C D : Category} {F : Functor C D} {G : Functor D C} (adj : (F ⊣ G)%functor).

  (** Duality for adjunctions. It follows from Hom_Adjunct_Duality. *)
  Definition Adjunct_Duality : (G^op ⊣ F^op)%functor := (Hom_Adj_to_Adj (Hom_Adjunct_Duality (Adj_to_Hom_Adj adj))).

End Adj_Duality.