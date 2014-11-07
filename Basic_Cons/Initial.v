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
  Init_of : Obj;
  Init_of_init : Initial C Init_of;

  I_morph := @i_morph _ _ Init_of_init
}.

Arguments Init_of C {_} : clear implicits.

Existing Instance Init_of_init.





