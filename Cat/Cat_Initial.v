Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Category.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Basic_Cons.Terminal.
Require Import Archetypal.Discr.Discr.

(** The unique functor from the initial category to any other. *)
Program Definition Functor_From_Empty_Cat (C' : Category) : (0 –≻ C')%functor :=
{|
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
|}.

Local Hint Extern 1 => cbn in *.

(** Empty Cat is the initial category. *)
Program Instance Cat_Init : (𝟘_ Cat)%object :=
{|
  terminal := 0%category;
  t_morph := fun x => Functor_From_Empty_Cat x
|}.