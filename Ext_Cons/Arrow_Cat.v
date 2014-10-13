Require Import Category.Core.

(*
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: for g : a → b and h : c → d, an arrow from g to h is a pair of arrows (f,f') s.t. the ollowing commutes:

             g
         a  –––→  b
         ∣        ∣
        f∣        ∣f'
         ↓        ↓
         c  ——–→ d
             h
*)

Section Arrow_Cat.

  Class Arrow `(C : Category Obj Hom) :=
    {
      Orig : Obj;
      Targ : Obj;
      Arr : Hom Orig Targ
    }.

  Arguments Orig {_ _ _} _ : clear implicits.
  Arguments Targ {_ _ _} _ : clear implicits.
  Arguments Arr {_ _ _} _ : clear implicits.

  Class Arrow_Hom `(C : Category Obj Hom) (a b : Arrow C) :=
    {
      Arr_H : Hom (Orig a) (Orig b);
      Arr_H' : Hom (Targ a) (Targ b);
      Arr_Hom_com : Arr_H' ∘ (Arr a) = (Arr b) ∘ Arr_H
    }.

  Arguments Arr_H {_ _ _ _ _} _ : clear implicits.
  Arguments Arr_H' {_ _ _ _ _} _ : clear implicits.
  Arguments Arr_Hom_com {_ _ _ _ _} _ : clear implicits.

  Context `(C : Category Obj Hom).

  Section Arrow_Hom_eq_simplify.
    Context {a b : Arrow C} (f g : Arrow_Hom C a b).

    Lemma Arrow_Hom_eq_simplify : Arr_H f = Arr_H g → Arr_H' f = Arr_H' g → f = g.
    Proof.
      intros H1 H2.
      destruct f as [fh fh' fc]; destruct g as [gh gh' gc]; simpl in *.
      destruct H1; destruct H2.
      destruct (proof_irrelevance _ fc gc).
      reflexivity.
    Qed.

  End Arrow_Hom_eq_simplify.

  Hint Extern 1 (?A = ?B :> Arrow_Hom _ _ _) => apply Arrow_Hom_eq_simplify; simpl.

  Section Compose_id.

    Context {x y z} (h : Arrow_Hom C x y) (h' : Arrow_Hom C y z).

    Program Instance Arrow_Hom_compose : Arrow_Hom C x z :=
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

    Program Instance Arrow_id : Arrow_Hom C x x :=
      {
        Arr_H := id;
        Arr_H' := id
      }.

    (* Arrow_Hom_id defined *)

  End Compose_id.

  Program Instance Arrow_Cat : Category (Arrow C) (Arrow_Hom C) :=
    {
      compose := λ _ _ _ f g, Arrow_Hom_compose f g;
      
      id := λ a, Arrow_id
    }.

  (* Arrow_Cat defined *)

End Arrow_Cat.

Hint Extern 1 (?A = ?B :> Arrow_Hom _ _ _) => apply Arrow_Hom_eq_simplify; simpl.

Arguments Orig {_ _ _} _ : clear implicits.
Arguments Targ {_ _ _} _ : clear implicits.
Arguments Arr {_ _ _} _ : clear implicits.

Arguments Arr_H {_ _ _ _ _} _ : clear implicits.
Arguments Arr_H' {_ _ _ _ _} _ : clear implicits.
Arguments Arr_Hom_com {_ _ _ _ _} _ : clear implicits.

