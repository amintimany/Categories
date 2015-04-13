Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Basic_Cons.Terminal.
Require Import Archetypal.Discr.

Program Instance Functor_To_1_Cat (C' : Category) : Functor C' 1%category :=
{
  FO := fun x => tt;
  FA := fun a b f => tt;
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
}.

(* Functor_To_Singleton_Cat defined *)

Program Instance Cat_Term : Terminal Cat :=
{
  terminal := 1%category;

  t_morph := fun x => Functor_To_1_Cat x
}.

Next Obligation. (* t_morph_unique *)
Proof.
  match goal with
    [|- ?A = ?B] =>
    cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
  end.
  extensionality x; extensionality y; extensionality h.
  apply JMeq_eq.
  match goal with
    [|- ?A ~= ?B] => destruct A as [[]]; destruct B as [[]]; trivial
  end.
  extensionality x.
  apply JMeq_eq.
  match goal with
    [|- ?A ~= ?B] => destruct A as [[]]; destruct B as [[]]; trivial
  end.
Qed.  

(* Cat_term defined *)

Section From_Term_Cat.
  Context {C : Category} (F : Functor 1 C).

  Theorem From_Term_Cat : ∀ h, F _a tt tt h = id.
  Proof.
    destruct h.
    change tt with (id 1 tt).
    rewrite F_id.
    trivial.
  Qed.

End From_Term_Cat.