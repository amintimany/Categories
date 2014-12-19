Require Import Category.Category.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Basic_Cons.Initial.
Require Import Categories.Discr.
Require Import Essentials.Empty.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Functor_From_Empty_Cat (C' : Category) : Functor 0%category C' :=
{
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
}.

(* Functor_From_Empty_Cat defined *)

Local Hint Extern 1 => simpl in *.

Program Instance Cat_Init : Initial Cat :=
{
  initial := (0%category);
  i_morph := fun x => Functor_From_Empty_Cat x
}.

(* Cat_init defined *)

Program Instance Cat_Has_Initial : Has_Initial Cat.





