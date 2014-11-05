Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Set Primitive Projections.

Set Universe Polymorphism.

Section Arrow.

  Class Arrow (C : Category) :=
    {
      Orig : Obj;
      Targ : Obj;
      Arr : Hom Orig Targ
    }.

  Arguments Orig {_} _ : clear implicits.
  Arguments Targ {_} _ : clear implicits.
  Arguments Arr {_} _ : clear implicits.

  Class Arrow_Hom {C : Category} (a b : Arrow C) :=
    {
      Arr_H : Hom (Orig a) (Orig b);
      Arr_H' : Hom (Targ a) (Targ b);
      Arr_Hom_com : Arr_H' ∘ (Arr a) = (Arr b) ∘ Arr_H
    }.
  Arguments Arr_H {_ _ _} _ : clear implicits.
  Arguments Arr_H' {_ _ _} _ : clear implicits.
  Arguments Arr_Hom_com {_ _ _} _ : clear implicits.

  Context (C : Category).

  Section Arrow_Hom_eq_simplify.
    Context {a b : Arrow C} (f g : Arrow_Hom a b).

    Lemma Arrow_Hom_eq_simplify : Arr_H f = Arr_H g → Arr_H' f = Arr_H' g → f = g.
    Proof.
      intros H1 H2.
      destruct f as [fh fh' fc]; destruct g as [gh gh' gc]; simpl in *.
      destruct H1; destruct H2.
      destruct (proof_irrelevance _ fc gc).
      reflexivity.
    Qed.

  End Arrow_Hom_eq_simplify.

  Section Compose_id.

    Context {x y z} (h : Arrow_Hom x y) (h' : Arrow_Hom y z).

    Program Instance Arrow_Hom_compose : Arrow_Hom x z :=
      {
        Arr_H := (Arr_H h') ∘ (Arr_H h);
        Arr_H' := (Arr_H' h') ∘ (Arr_H' h)
      }.

    Next Obligation. (* Arr_Hom_com *)
    Proof.
      destruct h as [hh hh' hc]; destruct h' as [h'h h'h' h'c].
      simpl.
      repeat rewrite assoc.
      rewrite hc.
      match goal with [|- ?A ∘ ?B ∘ ?C = _] => reveal_comp A B end.
      rewrite h'c.
      rewrite assoc; auto.
    Qed.

    (* Arrow_Hom_compose defined *)

    Program Instance Arrow_id : Arrow_Hom x x :=
      {
        Arr_H := id;
        Arr_H' := id
      }.

    (* Arrow_Hom_id defined *)

  End Compose_id.

End Arrow.

Hint Extern 1 (?A = ?B :> Arrow_Hom _ _) => apply Arrow_Hom_eq_simplify; simpl.

Arguments Orig {_} _ : clear implicits.
Arguments Targ {_} _ : clear implicits.
Arguments Arr {_} _ : clear implicits.

Arguments Arr_H {_ _ _} _ : clear implicits.
Arguments Arr_H' {_ _ _} _ : clear implicits.
Arguments Arr_Hom_com {_ _ _} _ : clear implicits.


Definition Arrow_to_Arrow_OP (C : Category) (ar : Arrow C) : Arrow (C ^op).
Proof.
  destruct ar.
  econstructor; eauto.
Defined.

Lemma Arrow_OP_Iso (C : Category) : @Isomorphic Type_Cat (Arrow C) (Arrow (C ^op)).
Proof.
  exists (Arrow_to_Arrow_OP C).
  set (ACO := Arrow_to_Arrow_OP (C ^op)).
  destruct C.
  exists ACO; extensionality x; destruct x; trivial.
Qed.