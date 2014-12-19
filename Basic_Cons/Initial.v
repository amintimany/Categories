Require Import Category.Main.
Require Import Functor.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Initial Object *)

Class Initial (C : Category) : Type :=
{
  initial : C;
  i_morph : ∀ (d : Obj), Hom initial d;
  i_morph_unique : ∀ (d : Obj) (f g : Hom initial d), f = g
}.

Coercion initial : Initial >-> Obj.

Theorem Initial_iso {C : Category} (I I' : Initial C) : I ≡ I'.
Proof.
  eapply (@Build_Isomorphism _ _ _ (i_morph _) (i_morph _)); apply i_morph_unique.
Qed.

Class Has_Initial (C : Category) : Type := has_initial : Initial C.





