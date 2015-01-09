Require Import Category.Main.
Require Import Functor.Main.

(* Terminal Object *)

Class Terminal (C : Category) : Type :=
{
  terminal : C;
  t_morph : ∀ (d : Obj), Hom d terminal;
  t_morph_unique : ∀ (d : Obj) (f g : Hom d terminal), f = g
}.

Arguments terminal {_} _.
Arguments t_morph {_} _ _.
Arguments t_morph_unique {_} _ _ _ _.

Coercion terminal : Terminal >-> Obj.

Theorem Terminal_iso {C : Category} (T T' : Terminal C) : T ≡ T'.
Proof.
  apply (Build_Isomorphism _ _ _ (t_morph _ _) (t_morph _ _)); apply t_morph_unique.
Qed.

(* Initial is the dual of Terminal. *)

Definition Initial (C : Category) := Terminal (C ^op).

Existing Class Initial.
