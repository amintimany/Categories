Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.

Class Sum `(C : Category Obj Hom) (c d p : Obj) : Type :=
{
  Inj_1 : Hom c p;
  Inj_2 : Hom d p;

  Sum_morph_ex : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), Hom p p';

  Sum_morph_com_1 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_1 = r1 ;
  
  Sum_morph_com_2 : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p'), (Sum_morph_ex p' r1 r2) ∘ Inj_2 = r2;
  
  Sum_morph_unique : ∀ (p' : Obj) (r1 : Hom c p') (r2 : Hom d p') (f g : Hom p p'), (f ∘ Inj_1 = r1) → (f ∘ Inj_2 = r2) → (g ∘ Inj_1 = r1) → (g ∘ Inj_2 = r2) → f = g
}.

Theorem Sum_iso `{C : Category Obj Hom} (c d p p': Obj) : Sum C c d p -> Sum C c d p' -> p ≡ p'.
Proof.
  intros [S1 S2 SX SXC1 SXC2 SU] [S1' S2' SX' SXC1' SXC2' SU'].
  exists (SX p' S1' S2'); exists (SX' p S1 S2);
  [apply (SU p S1 S2)| apply (SU' p' S1' S2')]; trivial;
  rewrite assoc; repeat (rewrite SXC1 || rewrite SXC2 || rewrite SXC1' || rewrite SXC2'); trivial.
Qed.


Definition Arrow_Sum `{C : Category Obj Hom}
           {a b c d x y : Obj}
           (sabx : Sum C a b x)
           (scdy : Sum C c d y)
           (f : Hom a c) (g : Hom b d)
: Hom x y :=
  @Sum_morph_ex _ _ C a b x sabx y ((@Inj_1 _ _ C c d y scdy) ∘ f) ((@Inj_2 _ _ C c d y scdy) ∘ g)
.

Program Instance Sum_Functor `{C : Category Obj Hom}
        (sm : Obj → Obj → Obj)
        (sm_sum : ∀ a b, Sum C a b (sm a b))
: Functor (Prod_Cat C C) C :=
{
  FO := fun x => sm (fst x) (snd x); 
  FA := fun a b f => Arrow_Sum (sm_sum _ _) (sm_sum _ _) (fst f) (snd f)
}.

Next Obligation. (* F_id *)  
Proof.
  simpl.
  match goal with
      [|- Arrow_Sum ?A ?A _ _ = _] =>
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
      | [|- context[(sm_sum ?A ?B)] ] =>
        let P1 := fresh "P1_0" in
        let P2 := fresh "P2_0" in
        let MEX := fresh "mex" in
        let MC1 := fresh "mc" in
        let MC2 := fresh "mc'" in
        let MU := fresh "mu" in
        destruct (sm_sum A B) as [P1 P2 MEX MC1 MC2 MU]
  end
  .
  simpl.
  eapply mu.
  rewrite mc; reflexivity.
  rewrite mc'; reflexivity.
  match goal with
      [|- (_ ∘ (mex ?B ?C ?D)) ∘ ?A = _] =>
      let H := fresh "H" in
      reveal_comp (mex B C D) A;
        assert(H := mc B C D);
        rewrite H;
        clear H
  end
  .
  match goal with
      [|- (mex1 ?C ?D ?E) ∘ ?B ∘ ?A = _] =>
      let H := fresh "H" in
      reveal_comp (mex1 C D E) B;
        assert(H := mc1 C D E);
        rewrite H;
        clear H
  end
  .
  rewrite assoc; trivial.
  match goal with
      [|- (_ ∘ (mex ?B ?C ?D)) ∘ ?A = _] =>
      let H := fresh "H" in
      reveal_comp (mex B C D) A;
        assert(H := mc' B C D);
        rewrite H;
        clear H
  end
  .
  match goal with
      [|- (mex1 ?C ?D ?E) ∘ ?B ∘ ?A = _] =>
      let H := fresh "H" in
      reveal_comp (mex1 C D E) B;
        assert(H := mc'1 C D E);
        rewrite H;
        clear H
  end
  .
  rewrite assoc; trivial.
Qed.

(* Sum_Functor defined *)

Class Has_Sums `(C : Category Obj Hom) : Type :=
{
  HS_sum : Obj → Obj → Obj;

  HS_sum_sum : forall a b, Sum C a b (HS_sum a b);

  HS_sum_ftor := Sum_Functor HS_sum HS_sum_sum
}.

Notation "x ⊕ y" := (HS_sum_ftor _o (x, y)).
Notation "〚 f , g 〛" := (HS_sum_ftor _a (_, _) (_, _) (f, g)).

Existing Instance HS_sum_sum.






