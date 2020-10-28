From Categories.Essentials Require Import Notations.
From Categories.Category Require Import Main.
From Categories.Functor Require Import Functor Functor_Ops.
From Categories.NatTrans Require Import Main.

Record Monad {C : Category} (F : (C --> C)%functor) := {
  monad_unit : NatTrans (Functor_id C) F;
  monad_mult : NatTrans (Functor_compose F F) F;
  monad_unit_mult_left :
    (monad_mult ∘ (monad_unit ∘_h (NatTrans_id F))
                ∘ (NatTrans_to_compose_id F))%nattrans =
    NatTrans_id F;
  monad_unit_mult_right :
    (monad_mult ∘ ((NatTrans_id F) ∘_h monad_unit)
                ∘ (NatTrans_to_id_compose F))%nattrans =
    NatTrans_id F;
  monad_mult_assoc :
    (monad_mult ∘ (monad_mult ∘_h (NatTrans_id F)))%nattrans =
    (monad_mult ∘ ((NatTrans_id F) ∘_h monad_mult)
                ∘ (NatTrans_Functor_assoc F F F))%nattrans; }.

Arguments monad_unit {_ _} _.
Arguments monad_mult {_ _} _.
Arguments monad_unit_mult_left {_ _} _.
Arguments monad_unit_mult_right {_ _} _.
Arguments monad_mult_assoc {_ _} _.
