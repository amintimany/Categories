Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Terminal.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Export NatTrans.NatTrans.
Require Export KanExt.Local KanExt.Global KanExt.GlobalDuality KanExt.GlobaltoLocal KanExt.LocaltoGlobal KanExt.LocalFacts.
Require Export Cat.Cat_Terminal.

Section Limit.
  Context {J C : Category} (D : Functor J C).

  Definition Cone := LoKan_Cone (Functor_To_1_Cat J) D.

  Existing Class Cone.

  Definition Cone_Morph := @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J) _ D.
  
  Existing Class Cone_Morph.
  
  Definition Limit : Type := Local_Right_KanExt (Functor_To_1_Cat J) D.

  Existing Class Limit.

  Definition limit_to_obj (l : Limit) : C := (cone_apex (LRKE l)) _o tt.

  Coercion limit_to_obj : Limit >-> Obj.

End Limit.

Program Instance Limit_Iso {J C : Category} {D : Functor J C} (l l' : Limit D) : l ≡≡ l' ::> C :=
  {
    iso_morphism := Trans (cone_morph (iso_morphism (Local_Right_KanExt_unique _ _ l l'))) tt;
    inverse_morphism := Trans (cone_morph (inverse_morphism (Local_Right_KanExt_unique _ _ l l'))) tt
  }.

Next Obligation.
Proof (f_equal (fun x : LoKan_Cone_Morph l l => Trans (cone_morph x) tt) (left_inverse (Local_Right_KanExt_unique _ _ l l'))).

Next Obligation.
Proof (f_equal (fun x : LoKan_Cone_Morph l' l' => Trans (cone_morph x) tt) (right_inverse (Local_Right_KanExt_unique _ _ l l'))).


Definition Has_Restr_Limits (C : Category) (P : Card_Restriction) := ∀ {J : Category} (D : Functor J C), P J → P (Arrow J) → Limit D.

Existing Class Has_Restr_Limits.

Definition Complete (C : Category) := ∀ J : Category, Right_KanExt (Functor_To_1_Cat J) C.

Existing Class Complete.

Definition Limit_of {C D : Category} {H : Complete D} (F : Functor C D) : Limit F := Global_to_Local_Right _ _ (H _) F.


Section Restricted_Limits_to_Complete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_Limits C P).

  Instance No_Restriction_Complete : (∀ t, P t) → Complete C := fun All_Ps J => Local_to_Global_Right _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_Limits_to_Complete.

Section Complete_to_Restricted_Limits.
  Context (C : Category) {CC : Complete C} (P : Card_Restriction).
  
  Instance Complete_Has_Restricted_Limits : Has_Restr_Limits C P := fun J D _ _ => Global_to_Local_Right _ _ (CC _) D.

End Complete_to_Restricted_Limits.

(* CoLimit *)

Definition CoCone {J C : Category} (D : Functor J C) := LoKan_Cone (Functor_To_1_Cat J^op) (Opposite_Functor D).

Existing Class CoCone.

Definition CoCone_Morph {J C : Category} (D : Functor J C) := @LoKan_Cone_Morph _ _ (Functor_To_1_Cat J^op) _ (Opposite_Functor D).

Existing Class CoCone_Morph.

Definition CoLimit {J C : Category} (D : Functor J C) := Local_Left_KanExt (Functor_To_1_Cat J) D.

Existing Class CoLimit.

Definition Has_Restr_CoLimits (C : Category) (P : Card_Restriction) := ∀ {J : Category} (D : Functor J C), P J → P (Arrow J) → CoLimit D.

Existing Class Has_Restr_CoLimits.

Definition CoComplete (C : Category) := ∀ J : Category, Left_KanExt (Functor_To_1_Cat J) C.

Existing Class CoComplete.

Definition CoLimit_of {C D : Category} {H : CoComplete D} (F : Functor C D) : CoLimit F := Global_to_Local_Left _ _ (H _) F.

Theorem Complete_to_CoComplete_Op {C : Category} {CC : Complete C} : CoComplete (C ^op).
Proof.
  intros D.
  apply (KanExt_Right_to_Left (Functor_To_1_Cat D^op)).
  apply CC.
Qed.

Theorem CoComplete_to_Complete_Op {C : Category} {CC : CoComplete C} : Complete (C ^op).
Proof.
  intros D.
  apply (KanExt_Left_to_Right (Functor_To_1_Cat D^op)).
  apply CC.
Qed.

Section Restricted_CoLimits_to_CoComplete.
  Context {C : Category} {P : Card_Restriction} (HRL : Has_Restr_CoLimits C P).

  Instance No_Restriction_CoComplete : (∀ t, P t) → CoComplete C := fun All_Ps J => Local_to_Global_Left _ _ (fun D => HRL _ D (All_Ps J) (All_Ps (Arrow J))).

End Restricted_CoLimits_to_CoComplete.

Section CoComplete_to_Restricted_CoLimits.
  Context (C : Category) {CC : CoComplete C} (P : Card_Restriction).
  
  Instance CoComplete_Has_Restricted_CoLimits : Has_Restr_CoLimits C P := fun J D _ _ => Global_to_Local_Left _ _ (CC _) D.

End CoComplete_to_Restricted_CoLimits.

Theorem Has_Restr_Limits_to_Has_Restr_CoLimits_Op {C : Category} {P : Card_Restriction} (HRL : Has_Restr_Limits C P) :  Has_Restr_CoLimits (C ^op) P.
Proof.
  intros D F H1 H2.
  apply HRL; trivial.
  eapply Card_Rest_Respect.
  apply Arrow_OP_Iso.
  trivial.
Qed.

Theorem Has_Restr_CoLimits_to_Has_Restr_Limits_Op {C : Category} {P : Card_Restriction} (HRL : Has_Restr_CoLimits C P) :  Has_Restr_Limits (C ^op) P.
Proof.
  intros D F H1 H2.
  apply (HRL _ (Opposite_Functor F)); trivial.
  eapply Card_Rest_Respect.
  apply Arrow_OP_Iso.
  trivial.
Qed.