Require Import Category.Main.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

(* Terminal Object *)

Class Terminal (C : Category) : Type :=
{
  terminal : C;
  t_morph : ∀ (d : Obj), Hom d terminal;
  t_morph_unique : ∀ (d : Obj) (f g : Hom d terminal), f = g
}.

Coercion terminal : Terminal >-> Obj.

Theorem Terminal_iso {C : Category} (T T' : Terminal C) : T ≡ T'.
Proof.
  apply (@Build_Isomorphism _ _ _ (t_morph _) (t_morph _)); apply t_morph_unique.
Qed.


