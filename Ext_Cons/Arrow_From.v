Require Import Category.Main.
Require Import Ext_Cons.Arrow.

Set Primitive Projections.

Set Universe Polymorphism.

Section Arrow_From.

  Class Arrow_From (C : Category) (c : Obj) :=
    {
      AF_Targ : Obj;
      AF_Arr : Hom c AF_Targ
    }.

  Arguments AF_Targ {_ _} _ : clear implicits.
  Arguments AF_Arr {_ _} _ : clear implicits.

  Program Instance Arrow_of_Arrow_From {C : Category} {c : Obj} (AF : Arrow_From C c) : Arrow C :=
    {
      Arr := AF_Arr AF
    }.

  Class Arrow_From_Hom {C : Category} {c : Obj} (a b : Arrow_From C c) :=
    {
      Arr_F_H' : Hom (AF_Targ a) (AF_Targ b);
      Arr_F_Hom_com : Arr_F_H' ∘ (AF_Arr a) = (AF_Arr b)
    }.
  Arguments Arr_F_H' {_ _ _ _} _ : clear implicits.
  Arguments Arr_F_Hom_com {_ _ _ _} _ : clear implicits.

  Program Instance Arrow_Hom_of_Arrow_From_Hom {C : Category} {c : Obj} {AF AF' : Arrow_From C c} (AFH : Arrow_From_Hom AF AF') : Arrow_Hom (Arrow_of_Arrow_From AF) (Arrow_of_Arrow_From AF') :=
    {
      Arr_H := id;
      Arr_H' := Arr_F_H' AFH
    }.

  Next Obligation. (* Arr_Hom_com *)
  Proof.
    rewrite Arr_F_Hom_com; auto.
  Qed.

  Context (C : Category).

  Section Arrow_From_Hom_eq_simplify.
    Context {c : Obj} {a b : Arrow_From C c} (f g : Arrow_From_Hom a b).

    Lemma Arrow_From_Hom_eq_simplify : Arr_F_H' f = Arr_F_H' g → f = g.
    Proof.
      intros H1.
      destruct f as [fh' fc]; destruct g as [gh' gc]; simpl in *.
      destruct H1.
      destruct (proof_irrelevance _ fc gc).
      reflexivity.
    Qed.

  End Arrow_From_Hom_eq_simplify.

  Section Compose_id.

    Context {c x y z} (h : @Arrow_From_Hom _ c x y) (h' : Arrow_From_Hom y z).

    Program Instance Arrow_From_Hom_compose : Arrow_From_Hom x z :=
      {
        Arr_F_H' := (Arr_F_H' h') ∘ (Arr_F_H' h)
      }.

    Next Obligation. (* Arr_Hom_com *)
    Proof.
      destruct h as [hh' hc]; destruct h' as [h'h' h'c].
      simpl.
      repeat rewrite assoc.
      rewrite hc; rewrite h'c; trivial.
    Qed.

    (* Arrow_Hom_compose defined *)

    Program Instance Arrow_From_id : Arrow_From_Hom x x :=
      {
        Arr_F_H' := id
      }.

    (* Arrow_Hom_id defined *)

  End Compose_id.

End Arrow_From.

Hint Extern 1 (?A = ?B :> Arrow_From_Hom _ _) => apply Arrow_From_Hom_eq_simplify; simpl.

Arguments AF_Targ {_ _} _ : clear implicits.
Arguments AF_Arr {_ _} _ : clear implicits.

Arguments Arr_F_H' {_ _ _ _} _ : clear implicits.
Arguments Arr_F_Hom_com {_ _ _ _} _ : clear implicits.

Coercion Arrow_of_Arrow_From : Arrow_From >-> Arrow.

Coercion Arrow_Hom_of_Arrow_From_Hom : Arrow_From_Hom >-> Arrow_Hom.