Require Import Category.Category.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Basic_Cons.Terminal.
Require Import Archetypal.Discr.
Require Import Essentials.Empty.

Program Instance Functor_From_Empty_Cat (C' : Category) : Functor 0%category C' :=
{
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
}.

(* Functor_From_Empty_Cat defined *)

Local Hint Extern 1 => cbn in *.

Program Instance Cat_Init : Initial Cat :=
{|
  terminal := (0%category);
  t_morph := fun x => Functor_From_Empty_Cat x
|}.

(* Cat_init defined *)






