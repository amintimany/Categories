From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import Cat.Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations.

(** The category of functors.

– Objects: functors from C to C'
– Arrows: natural transformations
*)
Definition Func_Cat (C C' : category) : category :=
{|
  obj := functor C C';

  hom := natural;

  compose := @natural_compose _ _;

  id := @natural_id _ _;

  assoc := fun _ _ _ _ _ _ _ => @natural_compose_assoc _ _ _ _ _ _ _ _ _;

  assoc_sym :=
    fun _ _ _ _ _ _ _ => eq_sym (@natural_compose_assoc _ _ _ _ _ _ _ _ _);

  left_id := @natural_id_unit_left _ _;

  right_id := @natural_id_unit_right _ _
|}.

(** Functor from functor category to its opposite. Maps each functor
      to its opposite. *)
Program Definition Op_Func_Cat_to_Func_Cat_Op (C D : category) : functor ((Func_Cat C D) ᴼᴾ) (Func_Cat (C ᴼᴾ) (D ᴼᴾ)) :=
  {|
    FO := opposite_functor;
    FA := fun _ _ => opposite_natural;
    F_id := fun _ => natural_id_op _;
    F_compose := fun _ _ _ _ _ => natural_compose_op _ _
  |}.

(** Functor from the opposite of a functor category to it. Maps each functor
    to its opposite. *)
Program Definition Func_Cat_Op_to_Op_Func_Cat (C D : category) : functor (Func_Cat (C ᴼᴾ) (D ᴼᴾ)) ((Func_Cat C D) ᴼᴾ) :=
  {|
    FO := opposite_functor;
    FA := fun _ _ => opposite_natural;
    F_id := fun F => natural_id_op F;
    F_compose := fun _ _ _ N N' => natural_compose_op N N'
  |}.

(** The opposite of the category of functors from C to D is naturally
      isomorphic to the category of functors from C^op to D^op. *)
Program Definition Func_Cat_Op_Iso (C D : category) : (((Func_Cat C D) ᴼᴾ)%category) ≃@{Cat} (Func_Cat (C ᴼᴾ) (D ᴼᴾ)) :=
  {|
    iso_morphism := Op_Func_Cat_to_Func_Cat_Op C D;
    inverse_morphism := Func_Cat_Op_to_Op_Func_Cat C D
  |}.
Solve All Obligations with simpl; auto.