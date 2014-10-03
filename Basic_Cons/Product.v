Require Import Category.Core.
Require Import Ext_Cons.Core.
Require Import Functor.Core.

(* Product Object *)


Class Product `(C : Category Obj Hom) (c d p : Obj) : Type :=
{
  Pi_1 : Hom p c;
  Pi_2 : Hom p d;

  Prod_morph_ex : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Hom p' p;

  Prod_morph_com_1 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_1 ∘ (Prod_morph_ex p' r1 r2) = r1;
  
  Prod_morph_com_2 : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), Pi_2 ∘ (Prod_morph_ex p' r1 r2) = r2;
  
  Prod_morph_unique : ∀ (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d) (f g : Hom p' p), (Pi_1 ∘ f = r1) → (Pi_2 ∘ f = r2) → (Pi_1 ∘ g = r1) → (Pi_2 ∘ g = r2) → f = g
}.

Theorem Product_iso `{C : Category Obj Hom} (c d p p': Obj) : Product C c d p → Product C c d p' → p ≡ p'.
Proof.
  intros [P1 P2 PX PXC1 PXC2 PU] [P1' P2' PX' PXC1' PXC2' PU'].
  exists (PX' p P1 P2); exists (PX p' P1' P2');
  [apply (PU p P1 P2) | apply (PU' p' P1' P2')]; trivial;
  (
    let simplify A B :=
        match A with
          | P1 => replace (A ∘ B) with P1'
          | P1' => replace (A ∘ B) with P1
          | P2 => replace (A ∘ B) with P2'
          | P2' => replace (A ∘ B) with P2
        end
    in
      repeat
        match goal with
          | [|- ?A ∘ ?B ∘ ?C = ?D] =>
            reveal_comp A B; simplify A B
          | [|- ?A ∘ ?B = ?C] => simplify A B
      end
  ); auto.
Qed.

Definition Arrow_Product `{C : Category Obj}
           {a b c d x y : Obj}
           (pabx : Product C a b x)
           (pcdy : Product C c d y)
           (f : Hom a c) (g : Hom b d)
: Hom x y :=
  @Prod_morph_ex _ _ C c d y pcdy x (f ∘ (@Pi_1 _ _ C a b x pabx)) (g ∘ (@Pi_2 _ _ C a b x pabx))
.

Program Instance Product_Functor `{C : Category Obj Hom} (pr : Obj → Obj → Obj) (pr_prod : ∀ a b, Product C a b (pr a b)) : Functor (Prod_Cat C C) C :=
{
  FO := fun x => pr (fst x) (snd x); 
  FA := fun a b f => Arrow_Product (pr_prod _ _) (pr_prod _ _) (fst f) (snd f)
}.

Next Obligation. (* F_id *)  
Proof.
  simpl.
  match goal with
      [|- Arrow_Product ?A ?A _ _ = _] =>
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
  simpl in *.
  repeat match goal with
      | [|- context[(pr_prod ?A ?B)] ] =>
        let P1 := fresh "P1_0" in
        let P2 := fresh "P2_0" in
        let MEX := fresh "mex" in
        let MC1 := fresh "mc" in
        let MC2 := fresh "mc'" in
        let MU := fresh "mu" in
        destruct (pr_prod A B) as [P1 P2 MEX MC1 MC2 MU]
  end
  .
  simpl.
  eapply mu0.
  rewrite mc0; reflexivity.
  rewrite mc'0; reflexivity.
  match goal with
      [|- ?A ∘ (mex0 ?B ?C ?D) ∘ _ = _] =>
      let H := fresh "H" in
      reveal_comp A (mex0 B C D);
        assert(H := mc0 B C D);
        rewrite H;
        clear H
  end
  .
  match goal with
      [|- (?A ∘ ?B) ∘ (mex1 ?C ?D ?E) = _] =>
      let H := fresh "H" in
      reveal_comp B (mex1 C D E);
        assert(H := mc1 C D E);
        rewrite H;
        clear H
  end
  .
  rewrite assoc; trivial.
  match goal with
      [|- ?A ∘ (mex0 ?B ?C ?D) ∘ _ = _] =>
      let H := fresh "H" in
      reveal_comp A (mex0 B C D);
        assert(H := mc'0 B C D);
        rewrite H;
        clear H
  end
  .
  match goal with
      [|- (?A ∘ ?B) ∘ (mex1 ?C ?D ?E) = _] =>
      let H := fresh "H" in
      reveal_comp B (mex1 C D E);
        assert(H := mc'1 C D E);
        rewrite H;
        clear H
  end
  .
  rewrite assoc; trivial.
Qed.

(* Product_Functor defined *)

Class Has_Products `(C : Category Obj Hom) : Type :=
{
  HP_prod : Obj → Obj → Obj;

  HP_prod_prod : ∀ a b, Product C a b (HP_prod a b);

  HP_prod_ftor := Product_Functor HP_prod HP_prod_prod
}.

Notation "x × y" := (HP_prod_ftor _o (x, y)).
Notation "≪ f , g ≫" := (HP_prod_ftor _a (_,_) (_,_) (f,g)).

Existing Instance HP_prod_prod.





