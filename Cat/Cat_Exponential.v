Require Import Cat.Cat_Product.

Require Import Coq.Logic.EqdepFacts.

Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans.

Set Primitive Projections.

Set Universe Polymorphism.

Local Obligation Tactic := idtac.

Program Instance Exp_Cat_eval (C C' : Category) : Functor (Prod_Cat (Func_Cat C C') C) C' :=
{
  FO := fun x => (fst x) _o (snd x);
  FA := fun A B f => ((fst B) _a _ _ (snd f)) ∘ (@Trans _ _ _ _ (fst f) _)
}.

Next Obligation. (* F_id *)
Proof.
  program_simpl.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros C C' [D1 x1] [D2 x2] [D3 x3] [f1 f2] [g1 g2].
  simpl in *.
  match goal with
      [|- ?A ∘ ?B ∘ ?D = ?E ∘ ?F ∘ ?G] =>
      reveal_comp A B; reveal_comp E F; apply f_equal
  end
  .
  match goal with
      [|- ?A ∘ ?B = _] =>
        match A with
            ?F _a _ _ ?X =>
            match goal with
                [H : NatTrans _ F |- _] =>
                let H' := fresh "H" in
                assert (H' := @Trans_com _ _ _ _ H _ _ X); symmetry in H'; rewrite H'
            end
        end
  end
  .
  rewrite F_compose.
  match goal with
      [|- ?A ∘ ?B ∘ ?D = _] =>
      reveal_comp A B; apply f_equal
  end
  .
  apply Trans_com.
Qed.

(* Exp_Cat_Eval defined *)

Local Obligation Tactic := program_simpl; auto.

Program Instance Exp_Cat_morph_ex_O {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') (a : @Obj C'') : Functor C C' :=
{
  FO := fun x => F _o (a, x);
  FA := fun _ _ f => F _a _ _ (@id _ a, f)
}.

(* Exp_Cat_morph_ex_O defined *)

Program Instance Exp_Cat_morph_ex_A {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') (a b : @Obj C'') (h : @Hom C'' a b) : NatTrans (Exp_Cat_morph_ex_O F a) (Exp_Cat_morph_ex_O F b) :=
{
  Trans := fun c => F _a _ _ (h, @id _ c)
}.

(* Exp_Cat_morph_ex_A defined *)

Program Instance Exp_Cat_morph_ex {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') : Functor C'' (Func_Cat C C') :=
{
  FO := Exp_Cat_morph_ex_O F;
  FA := Exp_Cat_morph_ex_A F
}.

Next Obligation. (* F_id *)
Proof.
  apply NatTrans_eq_simplify; trivial.
Qed.

Next Obligation. (* F_compose *)
Proof.
  apply NatTrans_eq_simplify; simpl.
  extensionality x.
  rewrite <- F_compose; simpl; simpl_ids; trivial.
Qed.

(* Exp_Cat_morph_ex *)

Lemma Exp_cat_morph_ex_eval_id {C C' C'' : Category} (u : Functor C'' (Func_Cat C C')) : u = Exp_Cat_morph_ex (Exp_Cat_eval C C' ∘ ((@Prod_of Cat Cat_Has_Products) _a (_, _) (_, _) (u, @id Cat C))).
Proof.
  match goal with
      |- ?A = ?B =>
      cut (A _o = B _o); [intros H4|]
  end.
  {
    apply Functor_eq_simplify.
    assumption.
    {
      apply FA_extensionality; trivial.
      {
        intros a b h.
        set (V := (u _o)).
        match type of H4 with
            ?A = ?B =>
            set (Va := eq_ind_r (λ f0 : Obj → Functor C C', f0 a = B a) eq_refl H4);
              set (Vb := eq_ind_r (λ f0 : Obj → Functor C C', f0 b = B b) eq_refl H4)
        end.
        hnf in Va, Vb.
        match goal with
            |- ?A ~= ?B =>
            cut (match Va in (_ = t) return @Hom (Func_Cat _ _) t _ with eq_refl => match Vb in (_ = t') return @Hom (Func_Cat _ _) _ t' with eq_refl => A end end = B); [intros H5; rewrite <- H5; clear H5; destruct H4; trivial|]
        end.
        apply NatTrans_eq_simplify.
        extensionality m.
        match goal with
            |- ?A = ?B =>
            cut (A ≃ B); [intros H5; rewrite H5; trivial|]
        end.
        apply (@JMeq_trans _ _ _ _ (Trans (u _a _ _ h) m)).
        destruct H4; trivial.
        simpl; rewrite F_id; auto.
      }
    }
  }
  {
    extensionality x.
    apply Functor_eq_simplify.
    reflexivity.
    FA_extensionality a b f.
    repeat (simpl; rewrite F_id); auto.
  }
Qed.

Local Obligation Tactic := idtac.

Program Instance Cat_Exponentials (C C' : Category) : Exponential Cat Cat_Has_Products C C' (Func_Cat C C') :=
{
  eval := Exp_Cat_eval C C';
  
  Exp_morph_ex := fun C'' F => @Exp_Cat_morph_ex C C' C'' F
}.

Next Obligation. (* Exp_morph_com *)
Proof.
  intros C C' z f.
  Functor_extensionality a b F.
  destruct a; trivial.
  simpl.
  rewrite <- F_compose.
  simpl; simpl_ids.
  destruct a; destruct b; destruct F; simpl; trivial.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
  intros C C' z f u u' H1 H2.
  program_simpl.
  assert (H3 := @f_equal _ _ Exp_Cat_morph_ex _ _ H2).
  repeat rewrite <- Exp_cat_morph_ex_eval_id in H3; trivial.
Qed.

(* Cat_Exponentials defined *)

Instance Cat_Has_Exponentials : Has_Exponentials Cat :=
{
  HE_exp := fun C C' => Func_Cat C C';
  HE_exp_exp := Cat_Exponentials
}.



