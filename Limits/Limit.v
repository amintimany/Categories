Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Terminal.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Export NatTrans.NatTrans.
Require Export KanExt.Local KanExt.Global KanExt.GlobalDuality
        KanExt.GlobaltoLocal KanExt.LocaltoGlobal KanExt.LocalFacts.Main.
Require Export Cat.Cat_Terminal.

Local Open Scope functor_scope.

(** Definition of limits and colimits using right and left kan extensions along the functor to
the terminal category. *)
Section Limit.
  Context {J C : Category} (D : J –≻ C).

  Definition Cone := LoKan_Cone (Functor_To_1_Cat J) D.

  Definition Cone_Morph Cn Cn' := @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J) _ D Cn Cn'.
  
  Definition Limit : Type := Local_Right_KanExt (Functor_To_1_Cat J) D.

  Definition limit_to_cone (l : Limit) : Cone := (LRKE l).

  Coercion limit_to_cone : Limit >-> Cone.
  
  Definition cone_to_obj (cn : Cone) : C := (cone_apex cn) _o tt.

  Coercion cone_to_obj : Cone >-> Obj.

End Limit.

(** Limits are unique up to isomorphism. *)
Program Definition Limit_Iso {J C : Category} {D : J –≻ C} (l l' : Limit D) :
  (l ≡≡ l' ::> C)%morphism :=
  {|
    iso_morphism :=
      Trans
        (cone_morph (iso_morphism (Local_Right_KanExt_unique _ _ l l')))
        tt;
    inverse_morphism :=
      Trans
        (cone_morph (inverse_morphism (Local_Right_KanExt_unique _ _ l l')))
        tt
  |}.

Next Obligation.
Proof (
    f_equal
      (fun x : LoKan_Cone_Morph l l => Trans (cone_morph x) tt)
      (left_inverse (Local_Right_KanExt_unique _ _ l l'))
  ).

Next Obligation.
Proof (
    f_equal
      (fun x : LoKan_Cone_Morph l' l' => Trans (cone_morph x) tt)
      (right_inverse (Local_Right_KanExt_unique _ _ l l'))
  ).

(** Proposition stating that category C has all limits of cardinality specified by P *)
Definition Has_Restr_Limits (C : Category) (P : Card_Restriction) :=
  ∀ {J : Category} (D : J –≻ C), P J → P (Arrow J) → Limit D.

(** A complete category has all limits – here it has global right kan extension *)
Definition Complete (C : Category) := ∀ J : Category, Right_KanExt (Functor_To_1_Cat J) C.

Existing Class Complete.

(** If a category is complete, we can produce all limits. *)
Definition Limit_of {C D : Category} {H : Complete D} (F : C –≻ D) : Limit F :=
  Global_to_Local_Right _ _ (H _) F.

(** A category having restricted limitis where the restriction always holds 
is just complete. *)
Section Restricted_Limits_to_Complete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_Limits C P).

  Definition No_Restriction_Complete : (∀ t, P t) → Complete C :=
    fun All_Ps J => Local_to_Global_Right _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_Limits_to_Complete.

(** A complete category has restricted limits for any restriction. *)
Section Complete_to_Restricted_Limits.
  Context (C : Category) {CC : Complete C} (P : Card_Restriction).
  
  Definition Complete_Has_Restricted_Limits : Has_Restr_Limits C P :=
    fun J D _ _ => Global_to_Local_Right _ _ (CC _) D.

End Complete_to_Restricted_Limits.

(** CoLimits *)

Definition CoCone {J C : Category} (D : J –≻ C) :=
  LoKan_Cone (Functor_To_1_Cat J^op) D^op.

Definition CoCone_Morph {J C : Category} (D : J –≻ C) Cn Cn' :=
  @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J^op) _ D^op Cn Cn'.

Definition CoLimit {J C : Category} (D : J –≻ C) := Local_Left_KanExt (Functor_To_1_Cat J) D.

(** Proposition stating that category C has all colimits of cardinality specified by P *)
Definition Has_Restr_CoLimits (C : Category) (P : Card_Restriction) :=
  ∀ {J : Category} (D : J –≻ C), P J → P (Arrow J) → CoLimit D.

(** A cocomplete category has all colimits – here it has global left kan extension *)
Definition CoComplete (C : Category) := ∀ J : Category, Left_KanExt (Functor_To_1_Cat J) C.

Existing Class CoComplete.

(** If a category is cocomplete, we can produce all colimits. *)
Definition CoLimit_of {C D : Category} {H : CoComplete D} (F : C –≻ D) : CoLimit F :=
  Global_to_Local_Left _ _ (H _) F.

(** If a category is complete, its dual is cocomplete *)
Definition Complete_to_CoComplete_Op {C : Category} {CC : Complete C} : CoComplete (C ^op) :=
  fun D => KanExt_Right_to_Left (Functor_To_1_Cat D ^op) C (CC (D ^op)%category).

(** If a category is cocomplete, its dual is complete *)
Definition CoComplete_to_Complete_Op {C : Category} {CC : CoComplete C} : Complete (C ^op) :=
    fun D => KanExt_Left_to_Right (Functor_To_1_Cat D ^op) C (CC (D ^op)%category).

(** A category having restricted colimitis where the restriction always holds 
is just cocomplete. *)
Section Restricted_CoLimits_to_CoComplete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_CoLimits C P).

  Definition No_Restriction_CoComplete : (∀ t, P t) → CoComplete C :=
    fun All_Ps J =>
      Local_to_Global_Left _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_CoLimits_to_CoComplete.

(** A cocomplete category has restricted colimits for any restriction. *)
Section CoComplete_to_Restricted_CoLimits.
  Context (C : Category) {CC : CoComplete C} (P : Card_Restriction).
  
  Definition CoComplete_Has_Restricted_CoLimits : Has_Restr_CoLimits C P :=
    fun J D _ _ => Global_to_Local_Left _ _ (CC _) D.

End CoComplete_to_Restricted_CoLimits.

(** If a category has restricted limits, its dual has restricted colomits *)
Definition Has_Restr_Limits_to_Has_Restr_CoLimits_Op
        {C : Category} {P : Card_Restriction}
        (HRL : Has_Restr_Limits C P) :
  Has_Restr_CoLimits (C ^op) P :=
  (fun (D : Category)
       (F : D –≻ C ^op)
       (H1 : P D)
       (H2 : P (Arrow D)) =>
     HRL
       (D ^op)%category
       (F ^op)%functor H1
       (Card_Rest_Respect P (Arrow D) (Arrow D ^op) (Arrow_OP_Iso D) H2)
  ).

(** If a category has restricted colimits, its dual has restricted lomits *)
Definition Has_Restr_CoLimits_to_Has_Restr_Limits_Op
        {C : Category}
        {P : Card_Restriction}
        (HRL : Has_Restr_CoLimits C P) :
  Has_Restr_Limits (C ^op) P :=
  (fun (D : Category)
       (F : D –≻ C ^op)
       (H1 : P D)
       (H2 : P (Arrow D)) =>
     HRL
       (D ^op)%category
       (F ^op)%functor
       H1
       (Card_Rest_Respect P (Arrow D) (Arrow D ^op) (Arrow_OP_Iso D) H2)
  ).