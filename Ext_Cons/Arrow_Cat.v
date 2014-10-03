Require Import Category.Core.

(*
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: g -> h is a pair of arrows (f,f') s.t. the ollowing commutes:

             g
         a  –––→  b
         ∣        ∣
        f∣        ∣f'
         ↓        ↓
         c  ——–→ d
             h

     The rest is trivial.
*)

Record ARROW `{Category Obj Hom} :=
  mkARROW{
      ARROW_ORIG : Obj;
      ARROW_TARG : Obj;
      ARROW_HOM : Hom ARROW_ORIG ARROW_TARG
    }.

Record ARROW_ARROW `{Category Obj Hom} (a b : ARROW) :=
  mkARROW_ARROW{
      ARROW_ARROW_HOM : Hom (ARROW_ORIG a) (ARROW_ORIG b);
      ARROW_ARROW_HOM' : Hom (ARROW_TARG a) (ARROW_TARG b);
      ARROW_ARROW_com : ARROW_ARROW_HOM' ∘ (ARROW_HOM a) = (ARROW_HOM b) ∘ (ARROW_ARROW_HOM)
    }.

Lemma ARROW_ARROW_eq_simplify `{Category Obj Hom} {a b : ARROW} (f g : ARROW_ARROW a b) : ARROW_ARROW_HOM _ _ f = ARROW_ARROW_HOM _ _ g → ARROW_ARROW_HOM' _ _ f = ARROW_ARROW_HOM' _ _ g → f = g.
Proof.
  intros H1 H2.
  destruct f as [fh fh' fc]; destruct g as [gh gh' gc]; simpl in *.
  destruct H1; destruct H2.
  destruct (proof_irrelevance _ fc gc).
  reflexivity.
Qed.


Program Definition ARROW_ARROW_compose `{C : Category Obj} {x y z} (h : ARROW_ARROW x y) (h' : ARROW_ARROW y z) : ARROW_ARROW x z :=
  mkARROW_ARROW _ _ _ x z
      ((ARROW_ARROW_HOM _ _ h') ∘ (ARROW_ARROW_HOM _ _ h))
      ((ARROW_ARROW_HOM' _ _ h') ∘ (ARROW_ARROW_HOM' _ _ h))
      _.

Next Obligation. (* ARROW_ARROW_com *)
Proof.
  destruct h as [hh hh' hc]; destruct h' as [h'h h'h' h'c].
  simpl.
  repeat rewrite assoc.
  rewrite hc.
  match goal with [|- ?A ∘ ?B ∘ ?C = _] => reveal_comp A B end.
  rewrite h'c.
  rewrite assoc; auto.
Qed.

(* ARROW_ARROW_compose defined *)

Program Definition ARROW_ARROW_id `{C : Category Obj} {x} : ARROW_ARROW x x :=
  mkARROW_ARROW _ _ _ x x id id _.

(* ARROW_ARROW_id defined *)

Program Instance Arrow_Cat `(C : Category Obj) : Category (@ARROW _ _ C) (λ f g, ARROW_ARROW f g) :=
{
  compose := λ _ _ _ f g, ARROW_ARROW_compose f g;
  
  id := λ a, ARROW_ARROW_id

}.

Next Obligation. (* assoc *)
Proof.
  destruct a as [aor atr ah]; destruct b as [bor btr bh];
    destruct c as [cor ctr ch]; destruct d as [dor dtr dh];
    destruct f as [fg fh' fc]; destruct g as [gg gh' gc]; destruct h as [hh hh' hc];
    simpl in *.
  
  apply ARROW_ARROW_eq_simplify; simpl; rewrite assoc; trivial.
Qed.

Next Obligation. (* assoc_sym *)
Proof.
  destruct a as [aor atr ah]; destruct b as [bor btr bh];
    destruct c as [cor ctr ch]; destruct d as [dor dtr dh];
    destruct f as [fg fh' fc]; destruct g as [gg gh' gc]; destruct h as [hh hh' hc];
    simpl in *.
  
  apply ARROW_ARROW_eq_simplify; simpl; rewrite assoc; trivial.
Qed.


Next Obligation. (* id_unit_left *)
Proof.
  destruct a as [aor atr ah]; destruct b as [bor btr bh];
    destruct h as [hg hh' hc];
    simpl in *.
  apply ARROW_ARROW_eq_simplify; simpl; auto.
Qed.

Next Obligation. (* id_unit_right *)
Proof.
  destruct a as [aor atr ah]; destruct b as [bor btr bh];
    destruct h as [hg hh' hc];
    simpl in *.
    apply ARROW_ARROW_eq_simplify; simpl; auto.
Qed.

(* Arrow_Cat defined *)