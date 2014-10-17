Require Import Category.Main.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.


Program Instance Hom_Func `(C : Category Obj Hom) : Functor (Prod_Cat C ^op C) Type_Cat :=
{
  FO := fun x => Hom (fst x) (snd x);
  FA := fun x y f => fun g => (@compose _ _ C _ _ _) (fst f) ((snd f) ∘ g)
}.

(* Hom_Func defined *)





