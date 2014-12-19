Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

(* Product Object *)

Class Product {C : Category} (c d : C) : Type :=
{
  product : C;

  Pi_1 : Hom product c;

  Pi_2 : Hom product d;

  Prod_morph_ex : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Hom p' product;

  Prod_morph_com_1 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_1 ∘ (Prod_morph_ex p' r1 r2) = r1;
  
  Prod_morph_com_2 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_2 ∘ (Prod_morph_ex p' r1 r2) = r2;
  
  Prod_morph_unique : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d) (f g : Hom p' product), (Pi_1 ∘ f = r1) → (Pi_2 ∘ f = r2) → (Pi_1 ∘ g = r1) → (Pi_2 ∘ g = r2) → f = g
}.

Coercion product : Product >-> Obj.

Theorem Product_iso {C : Category} (c d : Obj) (P : Product c d) (P' : Product c d) : P ≡ P'.
Proof.
  eapply (@Build_Isomorphism _ _ _ (@Prod_morph_ex _ _ _ P' P Pi_1 Pi_2) (@Prod_morph_ex _ _ _ P P' Pi_1 Pi_2));
  eapply Prod_morph_unique; eauto;
  rewrite <- assoc;
  repeat (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.

Class Has_Products (C : Category) : Type := has_products : ∀ a b, Product a b.

Program Instance Prod_Func {C : Category} {HP : Has_Products C} : Functor (Prod_Cat C C) C :=
{
  FO := fun x => HP (fst x) (snd x); 
  FA := fun a b f =>
       Prod_morph_ex _ ((fst f) ∘ Pi_1) ((snd f) ∘ Pi_2)
}.

Next Obligation. (* F_id *)  
Proof.
  eapply Prod_morph_unique; try reflexivity; [rewrite Prod_morph_com_1|rewrite Prod_morph_com_2]; auto.
Qed.  

Next Obligation. (* F_compose *)  
Proof.
  eapply Prod_morph_unique; try ((rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); reflexivity);
  repeat rewrite <- assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2);
  rewrite assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.


