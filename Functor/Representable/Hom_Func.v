Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.


(** The hom-functor is a functor that maps a pair of objects (a, b)
    (an object of the product category Cᵒᵖ×C) to the type of arrows
    from a to b. *)
Program Definition Hom_Func (C : Category) : ((C^op × C) –≻ Type_Cat)%functor :=
{|
  FO := fun x => Hom C (fst x) (snd x);
  FA := fun x y f => fun g => compose C (fst f) ((@compose (C^op) _ _ _) (snd f) g)
|}.




