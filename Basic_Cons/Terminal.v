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
  HT_term : Obj;
  HT_term_term : Terminal C HT_term;

  T_morph := @t_morph _ _ HT_term_term
}.

Existing Instance HT_term_term.

Notation "'_T_' D" := (@HT_term D _).


