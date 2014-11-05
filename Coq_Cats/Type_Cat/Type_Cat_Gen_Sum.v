Require Import Category.Main.
Require Import Basic_Cons.General_Sum.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Type_Cat_Gen_Sum (A : Type) (objs : A → Type) : General_Sum Type_Cat A objs {x : A & objs x}.

Next Obligation. (* Gen_Prod_morph_ex *)
Proof.
  match goal with
      [x : A |- _] =>
      exists x; trivial
  end.
Defined.

Next Obligation. (* Gen_Prod_morph_unique *)
Proof.
  cbv in *.
  match goal with
      [H : ∀ a : A, (λ x : objs a, ?f (existT (λ x0 : A, objs x0) a x)) = ?inj a, H' : ∀ a : A, (λ x : objs a, ?g (existT (λ x0 : A, objs x0) a x)) = ?inj a |- ?f = ?g] =>
      let u := fresh "u" in
      let a := fresh "a" in
      extensionality u; destruct u as [a u]; transitivity (inj a u); [rewrite <- H|rewrite <- H']; trivial
  end.
Qed.
