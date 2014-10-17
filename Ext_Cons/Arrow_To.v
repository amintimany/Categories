Require Import Category.Main.
Require Import Ext_Cons.Arrow.

Section Arrow_To.

  Class Arrow_To `(C : Category Obj Hom) (c : Obj) :=
    {
      AT_Orig : Obj;
      AT_Arr : Hom AT_Orig c
    }.

  Arguments AT_Orig {_ _ _ _} _ : clear implicits.
  Arguments AT_Arr {_ _ _ _} _ : clear implicits.

  Program Instance Arrow_of_Arrow_To `{C : Category Obj Hom} {c : Obj} (AF : Arrow_To C c) : Arrow C :=
    {
      Arr := AT_Arr AF
    }.

  Class Arrow_To_Hom `{C : Category Obj Hom} {c : Obj} (a b : Arrow_To C c) :=
    {
      Arr_T_H : Hom (AT_Orig a) (AT_Orig b);
      Arr_T_Hom_com : (AT_Arr a) = (AT_Arr b) ∘ Arr_T_H
    }.
  Arguments Arr_T_H {_ _ _ _ _ _} _ : clear implicits.
  Arguments Arr_T_Hom_com {_ _ _ _ _ _} _ : clear implicits.

  Program Instance Arrow_Hom_of_Arrow_To_Hom `{C : Category Obj Hom} {c : Obj} {AT AT' : Arrow_To C c} (ATH : Arrow_To_Hom AT AT') : Arrow_Hom (Arrow_of_Arrow_To AT) (Arrow_of_Arrow_To AT') :=
    {
      Arr_H' := id;
      Arr_H := Arr_T_H ATH
    }.

  Next Obligation. (* Arr_Hom_com *)
    rewrite (Arr_T_Hom_com ATH); auto.
  Qed.

  Context `(C : Category Obj Hom).

  Section Arrow_To_Hom_eq_simplify.
    Context {c : Obj} {a b : Arrow_To C c} (f g : Arrow_To_Hom a b).

    Lemma Arrow_To_Hom_eq_simplify : Arr_T_H f = Arr_T_H g → f = g.
    Proof.
      intros H1.
      destruct f as [fh' fc]; destruct g as [gh' gc]; simpl in *.
      destruct H1.
      destruct (proof_irrelevance _ fc gc).
      reflexivity.
    Qed.

  End Arrow_To_Hom_eq_simplify.

  Section Compose_id.

    Context {c x y z} (h : @Arrow_To_Hom _ _ _ c x y) (h' : Arrow_To_Hom y z).

    Program Instance Arrow_To_Hom_compose : Arrow_To_Hom x z :=
      {
        Arr_T_H := (Arr_T_H h') ∘ (Arr_T_H h)
      }.

    Next Obligation. (* Arr_Hom_com *)
    Proof.
      destruct h as [hh' hc]; destruct h' as [h'h' h'c].
      simpl.
      repeat rewrite <- assoc.
      rewrite hc; rewrite h'c; trivial.
    Qed.

    (* Arrow_Hom_compose defined *)

    Program Instance Arrow_To_id : Arrow_To_Hom x x :=
      {
        Arr_T_H := id
      }.

    (* Arrow_Hom_id defined *)

  End Compose_id.

End Arrow_To.

Hint Extern 1 (?A = ?B :> Arrow_To_Hom _ _) => apply Arrow_To_Hom_eq_simplify; simpl.

Arguments AT_Orig {_ _ _ _} _ : clear implicits.
Arguments AT_Arr {_ _ _ _} _ : clear implicits.

Arguments Arr_T_H {_ _ _ _ _ _} _ : clear implicits.
Arguments Arr_T_Hom_com {_ _ _ _ _ _} _ : clear implicits.

Coercion Arrow_of_Arrow_To : Arrow_To >-> Arrow.

Coercion Arrow_Hom_of_Arrow_To_Hom : Arrow_To_Hom >-> Arrow_Hom.