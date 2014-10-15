Require Import Category.Core.
Require Import Functor.Core.
Require Import Basic_Cons.Initial.
Require Import Basic_Cons.Terminal.

Require Import Limits.Limit.
Require Import Limits.CoLimit.

Section Cone_CoCone.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} {J : Category ObjJ HomJ}
          `{C : Category Obj Hom} {D : Functor J C} (cn : Cone D).

  Program Instance CoCone_of_Cone : CoCone (Opposite_Functor D) :=
    {
      CoCone_obj := Cone_obj cn;

      CoCone_arrow := Cone_arrow cn;
      
      CoCone_com := λ _ _ h, Cone_com cn h
    }.

End Cone_CoCone.

Section CoCone_Cone.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} {J : Category ObjJ HomJ}
          `{C : Category Obj Hom} {D : Functor J C} (ccn : CoCone D).

  Program Instance Cone_of_CoCone : Cone (Opposite_Functor D) :=
    {
      Cone_obj := CoCone_obj ccn;

      Cone_arrow := CoCone_arrow ccn;
      
      Cone_com := λ _ _ h, CoCone_com ccn h
    }.

End CoCone_Cone.

Section Cone_Morph_CoCone_Morph.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} {J : Category ObjJ HomJ}
          `{C : Category Obj Hom} {D : Functor J C} {cn cn' : Cone D} (h : Cone_Morph D cn cn').


  Program Instance CoCone_Morph_of_Cone_Morph : CoCone_Morph (Opposite_Functor D) (CoCone_of_Cone cn') (CoCone_of_Cone cn) :=
    {
      CoCone_Morph_arrow := Cone_Morph_arrow h;

      CoCone_Morph_com := Cone_Morph_com h
    }.

End Cone_Morph_CoCone_Morph.

Section CoCone_Morph_Cone_Morph.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} {J : Category ObjJ HomJ}
          `{C : Category Obj Hom} {D : Functor J C} {cn cn' : CoCone D} (h : CoCone_Morph D cn cn').

  Program Instance Cone_Morph_of_CoCone_Morph : Cone_Morph (Opposite_Functor D) (Cone_of_CoCone cn') (Cone_of_CoCone cn) :=
    {
      Cone_Morph_arrow := CoCone_Morph_arrow h;

      Cone_Morph_com := CoCone_Morph_com h
    }.

End CoCone_Morph_Cone_Morph.

Section Limit_CoLimit.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} 
          {J : Category ObjJ HomJ}
          `{C : Category Obj Hom}
          (D : Functor J C) (cn : Cone D)
          (L : Limit D cn).


  Program Instance CoLimit_of_Limit : CoLimit (Opposite_Functor D) (CoCone_of_Cone cn) :=
    {
      CoLim_init := {| i_morph := _; i_morph_unique := _ |}
    }.

  Next Obligation. (* i_morph *)
  Proof.
    destruct D; destruct C; destruct J.
    match goal with
        [d : CoCone _ |- _] =>
        let d' := fresh "d'" in
        set (d' := CoCone_Morph_of_Cone_Morph (@t_morph _ _ _ _ (@Lim_term _ _ _ _ _ _ _ _ L) (Cone_of_CoCone d)));
          destruct d; exact d'
    end.
  Defined.

  Next Obligation. (* i_morph_unique *)
    cut (Cone_Morph_of_CoCone_Morph f = Cone_Morph_of_CoCone_Morph g).
    {
      intros H.
      destruct f; destruct g.
      dependent destruction C.
      match goal with
          [|- Build_CoCone_Morph _ _ _ _ ?A = Build_CoCone_Morph _ _ _ _ ?B] =>
          destruct (proof_irrelevance _ A B)
      end.
      reflexivity.
    }
    {
      destruct C; destruct J; destruct D; destruct cn.
      apply (@t_morph_unique _ _ _ _ (@Lim_term _ _ _ _ _ _ _ _ L)).
    }
  Qed.

End Limit_CoLimit.

Section CoLimit_Limit.
  Context {ObjJ : Type} {HomJ : ObjJ → ObjJ → Type} 
          {J : Category ObjJ HomJ}
          `{C : Category Obj Hom}
          (D : Functor J C) (cn : CoCone D)
          (L : CoLimit D cn).

  Program Instance Limit_of_CoLimit : Limit (Opposite_Functor D) (Cone_of_CoCone cn) :=
    {
      Lim_term := {| t_morph := _; t_morph_unique := _ |}
    }.

  Next Obligation. (* t_morph *)
  Proof.
    destruct D; destruct C; destruct J.
    match goal with
        [d : Cone _ |- _] =>
        let d' := fresh "d'" in
        set (d' := Cone_Morph_of_CoCone_Morph (@i_morph _ _ _ _ (@CoLim_init _ _ _ _ _ _ _ _ L) (CoCone_of_Cone d)));
          destruct d; exact d'
    end.
  Defined.

  Next Obligation. (* t_morph_unique *)
    cut (CoCone_Morph_of_Cone_Morph f = CoCone_Morph_of_Cone_Morph g).
    {
      intros H.
      destruct f; destruct g.
      dependent destruction C.
      match goal with
          [|- Build_Cone_Morph _ _ _ _ ?A = Build_Cone_Morph _ _ _ _ ?B] =>
          destruct (proof_irrelevance _ A B)
      end.
      reflexivity.
    }
    {
      destruct C; destruct J; destruct D; destruct cn.
      apply (@i_morph_unique _ _ _ _ (@CoLim_init _ _ _ _ _ _ _ _ L)).
    }
  Qed.

End CoLimit_Limit.







