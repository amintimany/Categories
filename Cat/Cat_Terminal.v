Require Import Category.Core.
Require Import Functor.Core.
Require Import Cat.Cat.
Require Import Basic_Cons.Terminal.
Require Import Categories.Discr.

Program Instance Functor_To_1_Cat `(C' : Category Obj Hom) : Functor C' 1%category :=
{
  FO := fun x => tt;
  FA := fun a b f => Discr_id _ _
}.

(* Functor_To_Singleton_Cat defined *)

Program Instance Cat_Term : Terminal Cat (mkCAT _ _ 1%category) :=
{
  t_morph := fun x => Functor_To_1_Cat (THE_CAT x)
}.

Next Obligation. (* t_morph_unique *)
Proof.
  Functor_extensionality a b F.
  match goal with
      [|- ?A = ?B] =>
      destruct A; destruct B; trivial
  end.
  match goal with
      [|- ?A ~= ?B] =>
      destruct A as [[]]; destruct B as [[]]; trivial
  end.
Qed.

(* Cat_term defined *)

Program Instance Cat_Has_Terminal : Has_Terminal Cat.




