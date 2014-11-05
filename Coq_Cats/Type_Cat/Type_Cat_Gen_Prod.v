Require Import Category.Main.
Require Import Basic_Cons.General_Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Type_Cat_Gen_Prod (A : Type) (objs : A → Type) : General_Product Type_Cat A objs (∀ x, objs x).

Next Obligation. (* Gen_Prod_morph_unique *)
Proof.
  cbv in *.
  match goal with
      [H : ∀ a : A, (λ x : _, ?f x a) = ?prj a, H' : ∀ a : A, (λ x : _, ?g x a) = ?prj a |- ?f = ?g] =>
      let u := fresh "u" in
      let a := fresh "a" in
      extensionality u; extensionality a; transitivity (prj a u); [rewrite <- H|rewrite <- H']; trivial
  end.
Qed.
