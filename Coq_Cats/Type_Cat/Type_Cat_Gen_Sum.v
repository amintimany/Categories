Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Limits.Limit.
Require Import Archetypal.Discr.
Require Import Basic_Cons.Terminal.

Section Type_Cat_Gen_Sum.
  Context (A : Type) (map : A → Type).

  Local Notation Fm := (Discrete_Functor Type_Cat map) (only parsing).

  Program Instance Type_Cat_Gen_Sum_CoCone : CoCone Fm :=
    {
      cone := {x : A & Fm _o x}
    }.

  Next Obligation. (* CoCone_morph *)
  Proof.
    match goal with
        [x : A |- _] =>
        exists x; trivial
               end.
  Defined.

  Program Instance Type_Cat_Gen_Sum : CoLimit Fm :=
    {
      limit := {| terminal := Type_Cat_Gen_Sum_CoCone |}
    }.

  Next Obligation. (* t_morph *)
  Proof.
    eapply (@Build_Cone_Hom _ _ (Opposite_Functor Fm) _ Type_Cat_Gen_Sum_CoCone (fun v => match v with existT _ x fox => Cone_arrow d x fox end)); trivial.
  Qed.

  Next Obligation. (* Gen_Prod_morph_unique *)
  Proof.
    apply Cone_Morph_eq_simplify.
    let u := fresh "u" in
    let a := fresh "a" in
    extensionality u; destruct u as [a u]; transitivity (Cone_arrow d a u);
    [rewrite <- (Cone_Hom_com f)| rewrite <- (Cone_Hom_com g)]; trivial.
  Qed.

End Type_Cat_Gen_Sum.