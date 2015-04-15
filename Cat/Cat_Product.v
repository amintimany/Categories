Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.

(* Prod_Cat_morph_ex defined *)

Local Obligation Tactic := idtac.

Program Instance Cat_Products (C C' : Category) : @Product Cat C C' :=
{
  product := (Prod_Cat C C');

  Pi_1 := Cat_Proj1 C C';

  Pi_2 := Cat_Proj2 C C';

  Prod_morph_ex := fun P => fun F G =>  Functor_compose (Diag_Func P) (Prod_Functor F G)
}.

Next Obligation. (* Prod_morph_com1 *)
Proof.
  intros C C' p' r1 r2.
  match goal with
    [|- ?A = ?B] =>
    cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
  end.
  extensionality x; extensionality y; extensionality f.
  match goal with
    [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
    transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
  end.
  destruct W; trivial.
  apply JMeq_eq.
  destruct W; trivial.
Qed.

Next Obligation. (* Prod_morph_com2 *)
Proof.
  intros C C' p' r1 r2.
  match goal with
    [|- ?A = ?B] =>
    cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
  end.
  extensionality x; extensionality y; extensionality f.
  match goal with
    [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
    transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
  end.
  destruct W; trivial.
  apply JMeq_eq.
  destruct W; trivial.
Qed.

Next Obligation. (* Prod_morph_unique *)
Proof.
  intros C C' p' r1 r2 f g H1 H2 H3 H4.
  cbn in *.
  transitivity (Functor_compose (Diag_Func p') (Prod_Functor r1 r2)).
  + symmetry.
    rewrite <- H1, <- H2.
    apply Prod_Functor_Cat_Proj.
  + rewrite <- H3, <- H4.
    apply Prod_Functor_Cat_Proj.
Qed.


(* Cat_Products defined *)

Program Instance Cat_Has_Products : Has_Products Cat := fun _ _ => _.




