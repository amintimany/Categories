Require Import Category.Main.
Require Import Functor.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Initial Object *)


Class Initial (C : Category) (init : Obj) : Type :=
{
  i_morph : ∀ (d : Obj), Hom init d;
  i_morph_unique : ∀ (d : Obj) (f g : Hom init d), f = g
}.

Theorem Initial_iso {C : Category} (i i' : Obj) : Initial C i → Initial C i' → i ≡ i'.
Proof.
  intros [im imu] [im' imu'].
  exists (im i'); exists (im' i); trivial.
Qed.

Class Has_Initial (C : Category) : Type :=
{
  HI_init : Obj;
  HI_init_init : Initial C HI_init;

  I_morph := @i_morph _ _ HI_init_init
}.

Existing Instance HI_init_init.

Notation "'_I_' D" := (@HI_init D _).





