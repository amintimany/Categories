From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.

Section Hom_Func.
  Universe i j i' j'.
  Constraint i <= i', j <= j'.

(** The hom-functor is a functor that maps a pair of objects (a, b)
    (an object of the product category Cᵒᵖ×C) to the type of arrows
    from a to b. *)
Program Definition Hom_Func (C : Category@{i j}) :
  ((C^op × C) –≻ Type_Cat@{i' j'})%functor :=
{|
  FO := fun x => Hom C (fst x) (snd x);
  FA := fun x y f => fun g => compose C (fst f) ((@compose (C^op) _ _ _) (snd f) g)
|}.

End Hom_Func.


