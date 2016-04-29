Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat Cat.Terminal.
Require Import Limits.Limit.
Require Import KanExt.LocalFacts.From_Iso_Cat.
Require Import Cat.Cat_Iso.

(** Given I : C ≃ D for C and D categories we have limit of (F ∘ I)
    if we have limit of F. *)
Section Limit_From_Isomorphic_Cat.
Context {C D : Category}
        (I : (C ≃≃ D ::> Cat)%isomorphism)
        {E : Category}
        {F : (D –≻ E)%functor}
        (L : Limit F)
.

Definition Limit_From_Isomorphic_Cat : Limit (F ∘ (iso_morphism I)) :=
  Local_Right_KanExt_Iso_along
    (
      Functor_To_1_Cat_Iso
        (Functor_To_1_Cat C)
        (Functor_To_1_Cat D ∘ (iso_morphism I))
    )
    (KanExt_From_Isomorphic_Cat I (Functor_To_1_Cat D) F L)
.

End Limit_From_Isomorphic_Cat.

(** Given I : C ≃ D for C and D categories we have colimit of (F ∘ I)
    if we have colimit of F. *)
Section CoLimit_From_Isomorphic_Cat.
Context {C D : Category}
        (I : (C ≃≃ D ::> Cat)%isomorphism)
        {E : Category}
        {F : (D –≻ E)%functor}
        (L : CoLimit F)
.

Definition CoLimit_From_Isomorphic_Cat : CoLimit (F ∘ (iso_morphism I)) :=
  Limit_From_Isomorphic_Cat (Opposite_Cat_Iso I) L
.

End CoLimit_From_Isomorphic_Cat.