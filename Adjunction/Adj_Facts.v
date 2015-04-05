Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction Adjunction.Duality.
Require Import Cat.Cat.

Section Hom_Adjunct_left_iso.
  Context {C D : Category} {F F' : Functor C D} (N : F' ≡≡ F ::> Func_Cat _ _) {G : Functor D C} (adj : Hom_Adjunct F G).

  Definition Hom_Adjunct_left_iso : Hom_Adjunct F' G := NatIso_compose (NatIso_hor_comp (Prod_Functor_NatIso (Opposite_NatIso N) (NatTrans_id_Iso (Functor_id D))) (NatTrans_id_Iso (Hom_Func D))) adj.

End Hom_Adjunct_left_iso.

Section Hom_Adjunct_right_iso.
  Context {C D : Category} {F : Functor C D} {G G' : Functor D C} (N : G ≡≡ G' ::> Func_Cat _ _) (adj : Hom_Adjunct F G).

  Definition Hom_Adjunct_right_iso : Hom_Adjunct F G' := Hom_Adjunct_Duality (Hom_Adjunct_left_iso (Inverse_Isomorphism (Opposite_NatIso N)) (Hom_Adjunct_Duality adj)).

End Hom_Adjunct_right_iso.

Section Adjunct_left_iso.
  Context {C D : Category} (F F' : Functor C D) (N : F' ≡≡ F ::> Func_Cat _ _) (G : Functor D C) (adj : Adjunct F G).

  Definition Adjunct_left_iso : Adjunct F' G := Hom_Adj_to_Adj (Hom_Adjunct_left_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_left_iso.

Section Adjunct_right_iso.
  Context {C D : Category} (F : Functor C D) (G G' : Functor D C) (N : G ≡≡ G' ::> Func_Cat _ _) (adj : Adjunct F G).

  Definition Adjunct_right_iso : Adjunct F G' := Hom_Adj_to_Adj (Hom_Adjunct_right_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_right_iso.

