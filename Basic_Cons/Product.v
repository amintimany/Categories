Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Product Object *)


Class Product (C : Category) (c d p : Obj) : Type :=
{
  Pi_1 : Hom p c;
  Pi_2 : Hom p d;

  Prod_morph_ex : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Hom p' p;

  Prod_morph_com_1 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_1 ∘ (Prod_morph_ex p' r1 r2) = r1;
  
  Prod_morph_com_2 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_2 ∘ (Prod_morph_ex p' r1 r2) = r2;
  
  Prod_morph_unique : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d) (f g : Hom p' p), (Pi_1 ∘ f = r1) → (Pi_2 ∘ f = r2) → (Pi_1 ∘ g = r1) → (Pi_2 ∘ g = r2) → f = g
}.

Theorem Product_iso {C : Category} (c d p p': Obj) : Product C c d p → Product C c d p' → p ≡ p'.
Proof.
  intros [P1 P2 PX PXC1 PXC2 PU] [P1' P2' PX' PXC1' PXC2' PU'].
  exists (PX' p P1 P2); exists (PX p' P1' P2');
  [apply (PU p P1 P2) | apply (PU' p' P1' P2')]; trivial;
  rewrite <- assoc;
  repeat (rewrite PXC1 || rewrite PXC2 || rewrite PXC1' || rewrite PXC2'); trivial.
Qed.

Program Instance Product_Functor {C : Category} (pr : Obj → Obj → Obj) (pr_prod : ∀ a b, Product C a b (pr a b)) : Functor (Prod_Cat C C) C :=
{
  FO := fun x => pr (fst x) (snd x); 
  FA := fun a b f =>
       @Prod_morph_ex C _ _ _ (pr_prod _ _) _ ((fst f) ∘ (@Pi_1 C _ _ _ (pr_prod _ _))) ((snd f) ∘ (@Pi_2 C _ _ _ (pr_prod _ _)))
}.

Next Obligation. (* F_id *)  
Proof.
  simpl.
  match goal with
      [|- @Prod_morph_ex _ _ _ _ ?A _ _ _ = _] =>
      destruct A as [p1 p2 mex mc1 mc2 mu]
  end
  .
  simpl.
  eapply mu.
  rewrite mc1; reflexivity.
  rewrite mc2; reflexivity.
  transitivity p1; auto.
  transitivity p2; auto.
Qed.

Next Obligation. (* F_compose *)  
Proof.
  eapply Prod_morph_unique.
  + rewrite Prod_morph_com_1; reflexivity.
  + rewrite Prod_morph_com_2; reflexivity.
  + repeat rewrite <- assoc.
    rewrite Prod_morph_com_1.
    rewrite assoc.
    rewrite Prod_morph_com_1.
    auto.
  + repeat rewrite <- assoc.
    rewrite Prod_morph_com_2.
    rewrite assoc.
    rewrite Prod_morph_com_2.
    auto.
Qed.

(* Product_Functor defined *)

Class Has_Products (C : Category) : Type :=
{
  HP_prod : Obj → Obj → Obj;

  HP_prod_prod : ∀ a b, Product C a b (HP_prod a b);

  Prod_of := Product_Functor HP_prod HP_prod_prod
}.

Existing Instance HP_prod_prod.





