Require Import Category.Main.
Require Import Functor.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Terminal Object *)

Class Terminal (C : Category) (term : Obj) : Type :=
{
  t_morph : ∀ (d : Obj), Hom d term;
  t_morph_unique : ∀ (d : Obj) (f g : Hom d term), f = g
}.

Theorem Terminal_iso {C : Category} (t t' : Obj) : Terminal C t → Terminal C t' → t ≡ t'.
Proof.
  intros [tm tmu] [tm' tmu'].
  exists (tm' t); exists (tm t'); trivial.
Qed.

Class Has_Terminal (C : Category) : Type :=
{
  Term_of : Obj;
  Term_of_term : Terminal C Term_of;

  T_morph := @t_morph _ _ Term_of_term
}.

Arguments Term_of C {_} : clear implicits.

Existing Instance Term_of_term.

