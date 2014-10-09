Require Import Category.Core.
Require Import Ext_Cons.Core.
Require Import Functor.Core.

(* Terminal Object *)

Class Terminal `(C : Category Obj Hom) (term : Obj) : Type :=
{
  t_morph : ∀ (d : Obj), Hom d term;
  t_morph_unique : ∀ (d : Obj) (f g : Hom d term), f = g
}.

Theorem Terminal_iso `{C : Category Obj Hom} (t t' : Obj) : Terminal C t → Terminal C t' → t ≡ t'.
Proof.
  intros [tm tmu] [tm' tmu'].
  exists (tm' t); exists (tm t'); trivial.
Qed.

Class Has_Terminal `(C : Category Obj Hom) : Type :=
{
  HT_term : Obj;
  HT_term_term : Terminal C HT_term;

  T_morph := @t_morph _ _ _ _ HT_term_term
}.

Existing Instance HT_term_term.

Notation "'_T_' D" := (@HT_term _ _ D _).


