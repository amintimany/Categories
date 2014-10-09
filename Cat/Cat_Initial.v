Require Import Category.Category.
Require Import Functor.Core.
Require Import Cat.Cat.
Require Import Basic_Cons.Initial.
Require Import Categories.Discr.
Require Import Essentials.Empty.

Program Instance Functor_From_Empty_Cat `(C' : Category Obj Hom) : Functor 0%category C' :=
{
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
}.

(* Functor_From_Empty_Cat defined *)

Program Instance Cat_Init : Initial Cat (mkCAT _ _ 0%category) :=
{
  i_morph := fun x => Functor_From_Empty_Cat (THE_CAT x)
}.

Next Obligation. (* i_morph_unique *)
Proof.
  Functor_extensionality a b F; simpl in *; auto.
Qed.

(* Cat_init defined *)

Program Instance Cat_Has_Initial : Has_Initial Cat.





