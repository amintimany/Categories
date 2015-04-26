Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

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
      destruct h as [hh hh' hc]; destruct h' as [h'h h'h' h'c]; simpl.
      rewrite assoc.
      rewrite hc.
      match goal with [|- ?A ∘ ?B ∘ ?C = _] => reveal_comp A B end.
      rewrite h'c.
      auto.
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

Lemma Arrow_OP_Iso (C : Category) : (Arrow C) ≡≡ (Arrow (C ^op)) ::> Type_Cat.
Proof.
  eapply (Build_Isomorphism Type_Cat _ _ (Arrow_to_Arrow_OP C) (Arrow_to_Arrow_OP (C ^op))); auto.
Qed.

Definition Arrow_Conv {C : Category} (a b : Arrow C) (HO : Orig a = Orig b) (HT : Targ a = Targ b) :=
  {|
    Orig := Orig b;
    Targ := Targ b;
    Arr :=
      match HO in _ = u return Hom u _
      with eq_refl =>
           match HT in _ = v return Hom _ v
           with
             eq_refl => (Arr a)
           end
      end
  |}.

Theorem Arrow_Conv_eq {C : Category} (a b : Arrow C) (HO : Orig a = Orig b) (HT : Targ a = Targ b) (H : a = b) : (Arrow_Conv a b HO HT) = b.
Proof.
  destruct H.
  unfold Arrow_Conv.
  apply JMeq_eq.
  destruct HO.
  destruct HT.
  trivial.
Qed.

Theorem Arrow_Conv_Arr_eq {C : Category} (a b : Arrow C) (HO : Orig a = Orig b) (HT : Targ a = Targ b) (H : a = b) : Arr (Arrow_Conv a b HO HT) = Arr b.
Proof.
  destruct H.
  unfold Arrow_Conv.
  cbn.
  apply JMeq_eq.
  destruct HO.
  destruct HT.
  trivial.
Qed.
             
Local Obligation Tactic := idtac.

Program Instance Arrow_Inclusion_Monic (C : Category) (x y : C) : @Monic Type_Cat (Hom x y) (Arrow C) :=
  {
    mono_morphism := fun w => {|Arr := w|}
  }.

Next Obligation.
Proof.
  intros C x y c g h H.
  cbn in H.
  extensionality m.
  set (W := (equal_f H m)); clearbody W; clear H; cbn in W.
  match type of W with
    ?A = ?B =>
    apply (Arrow_Conv_Arr_eq A B eq_refl eq_refl W)
  end.
Qed.
