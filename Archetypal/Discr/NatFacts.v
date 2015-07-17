Require Import Category.Main.
Require Import Functor.Main.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Cat.Cat Cat.Cat_Iso.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Archetypal.Discr.Discr.

(** This module contains facts about discrete categories and discrete functors involving
natural transformations. *)

(** The fact that dicrete functor from (Discr_Cat A) to Cᵒᵖ is naturally isomorphic to
the opposite of discrete-opposite functor from (Discr_Cat A)ᵒᵖ to C. *)
Section Discr_Func_Iso.
  Context {C : Category} {A : Type} (Omap : A → C).

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Discr_Func_Iso :
    (
      (@Discr_Func C^op A Omap) ≡≡ ((@Discr_Func_op C A Omap)^op)%functor ::> Func_Cat _ _
    )%morphism
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun _ => id
          |};
        inverse_morphism :=
          {|
            Trans := fun _ => id
          |}
      |}
  .
    
End Discr_Func_Iso.

Section Discr_Func_Arrow_Iso.
  Context {C D : Category} (arrmap : (Arrow C^op) → D).

  (**  *)
  Definition Discr_Cat_ArrowOp_Discr_Cat_Arrow_Op :
    (((Discr_Cat (Arrow C^op))^op)%category
                                  ≡≡ ((Discr_Cat (Arrow C))^op)%category ::> Cat)%morphism
    :=
      Opposite_Cat_Iso (Discr_Cat_Iso (Inverse_Isomorphism (Arrow_OP_Iso C)))
  .

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

  Program Definition Discr_Func_Arrow_Iso :
    (
      (
        (Discr_Func_op (fun x : Arrow C => arrmap (Arrow_to_Arrow_OP C x)))
          ∘ Discr_Cat_ArrowOp_Discr_Cat_Arrow_Op
      )
        ≡≡ ((@Discr_Func_op D (Arrow C^op) arrmap))%functor ::> Func_Cat _ _
    )%morphism
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun c => id
          |};
        inverse_morphism :=
          {|
            Trans := fun c => id
          |}
      |}
  .
    
End Discr_Func_Arrow_Iso.

Local Hint Extern 1 => match goal with [z : Arrow (Discr_Cat _) |- _] => destruct z as [? ? []] end.

(** The fact that in discrete categories object type and arrow type are isomorphic. *)
Program Definition Discr_Hom_Iso (A : Type) :
  (A ≡≡ Arrow (Discr_Cat A) ::> Type_Cat)%morphism :=
  (Build_Isomorphism
     Type_Cat
     _
     _
     (fun a => (Build_Arrow (Discr_Cat A) _ _ (eq_refl a)))
     (fun a : (Arrow (Discr_Cat _)) => Orig a)
     _
     _
  ).

Section Discretize.
  Context {C D : Category} {F G : (C –≻ D)%functor} (N : (F –≻ G)%nattrans).

  (** Discretizes a natural transformation. That is, it forgets about the arrow maps
of the functors and assumes the functors are just discrete functors, retaining the
object maps of the functors. *)
  Program Definition Discretize :
    ((Discr_Func (F _o)%object) –≻ (Discr_Func (G _o)%object))%nattrans
    :=
    {|
      Trans := Trans N
    |}.
  
End Discretize.