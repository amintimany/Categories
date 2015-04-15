Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Functor.Main.

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

Arguments Product _ _ _, {_} _ _.

Arguments Pi_1 {_ _ _ _}, {_ _ _} _.
Arguments Pi_2 {_ _ _ _}, {_ _ _} _.
Arguments Prod_morph_ex {_ _ _} _ _ _ _.
Arguments Prod_morph_com_1 {_ _ _} _ _ _ _.
Arguments Prod_morph_com_1 {_ _ _} _ _ _ _.
Arguments Prod_morph_unique {_ _ _} _ _ _ _ _ _ _ _ _ _.

Coercion product : Product >-> Obj.

Theorem Product_iso {C : Category} (c d : Obj) (P : Product c d) (P' : Product c d) : P ≡ P'.
Proof.
  eapply (Build_Isomorphism _ _ _ (Prod_morph_ex P' P Pi_1 Pi_2) (Prod_morph_ex P P' Pi_1 Pi_2));
  eapply Prod_morph_unique; eauto;
  rewrite <- assoc;
  repeat (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.

Definition Has_Products (C : Category) : Type := ∀ a b, Product a b.

Existing Class Has_Products.

Local Obligation Tactic := idtac.

Program Instance Prod_Func (C : Category) {HP : Has_Products C} : Functor (Prod_Cat C C) C :=
{
  FO := fun x => HP (fst x) (snd x); 
  FA := fun a b f => Prod_morph_ex _ _ ((fst f) ∘ Pi_1) ((snd f) ∘ Pi_2)
}.

Next Obligation. (* F_id *)  
Proof.
  intros.
  eapply Prod_morph_unique; try reflexivity; [rewrite Prod_morph_com_1|rewrite Prod_morph_com_2]; auto.
Qed.  

Next Obligation. (* F_compose *)  
Proof.
  intros.
  cbn.
  eapply Prod_morph_unique; try ((rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); reflexivity);
  repeat rewrite <- assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2);
  rewrite assoc; (rewrite Prod_morph_com_1 || rewrite Prod_morph_com_2); auto.
Qed.

Arguments Prod_Func _ _, _ {_}.

(* Sum is the dual of equalzier *)

Definition Sum (C : Category) := @Product C^op.

Existing Class Sum.

Arguments Sum _ _ _, {_} _ _.

Definition Has_Sums (C : Category) : Type :=  ∀ (a b : C), Sum a b.

Existing Class Has_Sums.

Instance Sum_Func {C : Category} {HS : Has_Sums C} : Functor (Prod_Cat C C) C := Opposite_Functor (Functor_compose (iso_morphism (Opposite_Prod C C)) (Prod_Func C^op HS)).

Arguments Sum_Func _ _, _ {_}.

