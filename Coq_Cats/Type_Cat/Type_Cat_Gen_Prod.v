Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Limits.Limit.
Require Import Categories.Discr.
Require Import Basic_Cons.Terminal.

Set Primitive Projections.

Set Universe Polymorphism.

Section Type_Cat_Gen_Prod.
  Context (A : Type) (map : A → Type).

  Local Notation Fm := (Discrete_Functor Type_Cat map) (only parsing).

  Program Instance Type_Cat_Gen_Prod_Cone : Cone Fm :=
    {
      cone := ∀ x : A, Fm _o x
    }.

  Program Instance Type_Cat_Gen_Prod : Limit Fm :=
    {
      limit := {| terminal := Type_Cat_Gen_Prod_Cone |}
    }.

  Next Obligation. (* t_morph *)
  Proof.
    eapply (@Build_Cone_Hom _ _ Fm _ Type_Cat_Gen_Prod_Cone (fun v x => Cone_arrow d x v)); trivial.
  Qed.

  Next Obligation. (* Gen_Prod_morph_unique *)
  Proof.
    apply Cone_Morph_eq_simplify.
    let u := fresh "u" in
    let a := fresh "a" in
    extensionality u; extensionality a; transitivity (Cone_arrow d a u);
    [rewrite <- (Cone_Hom_com f)| rewrite <- (Cone_Hom_com g)]; trivial.
  Qed.

End Type_Cat_Gen_Prod.