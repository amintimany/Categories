Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans.
Require Import Cat.Cat_Product.

Local Obligation Tactic := idtac.

Program Instance Exp_Cat_Eval (C C' : Category) : Functor (Prod_Cat (Func_Cat C C') C) C' :=
{
  FO := fun x => (fst x) _o (snd x);
  FA := fun A B f => ((fst B) _a _ _ (snd f)) ∘ (@Trans _ _ _ _ (fst f) _)
}.

Next Obligation. (* F_id *)
Proof.
  cbn; auto.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros C C' [a1 a2] [b1 b2] [c1 c2] [f1 f2] [g1 g2].
  cbn.
  repeat rewrite F_compose.
  repeat rewrite assoc.
  match goal with
      [|- ?A ∘ ?B = ?A ∘ ?C] => cutrewrite (B = C); trivial
  end.
  repeat rewrite assoc_sym.
  match goal with
      [|- ?A ∘ ?B = ?C ∘ ?B] => cutrewrite (A = C); trivial
  end.
  rewrite Trans_com; trivial.
Qed.

(* Exp_Cat_Eval defined *)

Local Obligation Tactic := program_simpl.

Program Instance Exp_Cat_morph_ex_A {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') (a b : C'') (h : Hom a b) : NatTrans (Fix_Bi_Func_1 a F) (Fix_Bi_Func_1 b F) :=
{
  Trans := fun c => F _a _ _ (h, @id _ c)
}.

(* Exp_Cat_morph_ex_A defined *)

Program Instance Exp_Cat_morph_ex {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') : Functor C'' (Func_Cat C C') :=
{
  FO := fun a => Fix_Bi_Func_1 a F;
  FA := Exp_Cat_morph_ex_A F
}.

Next Obligation. (* F_compose *)
Proof.
  apply NatTrans_eq_simplify; cbn; auto.
Qed.

Next Obligation. (* F_id *)
Proof.
  apply NatTrans_eq_simplify; cbn; auto.
Qed.

(* Exp_Cat_morph_ex *)

Lemma Exp_cat_morph_ex_eval_id {C C' C'' : Category} (u : Functor C'' (Func_Cat C C')) : u = Exp_Cat_morph_ex (Exp_Cat_Eval C C' ∘ ((Prod_Func _ Cat_Has_Products) _a (_, _) (_, _) (u, id Cat C))).
Proof.
  match goal with
      |- ?A = ?B =>
      cut (A _o = B _o); [intros H4|]
  end.
  {
    apply (Functor_eq_simplify _ _ H4).
    extensionality a; extensionality b; extensionality h.
    cbn.
    apply NatTrans_eq_simplify.
    extensionality m.
    match goal with
      |- ?A = ?B =>
      cut (A ≃ B); [intros H5; rewrite H5; trivial|]
    end.
    apply (@JMeq_trans _ _ _ _ (Trans (u _a _ _ h) m)).
    destruct H4; trivial.
    cbn; rewrite F_id; auto.
  }    
  {
    extensionality x.
    
    match goal with
      [|- ?A = ?B] =>
      set (W := eq_refl : A _o = B _o); apply (Functor_eq_simplify _ _ W); trivial
    end.
    extensionality a; extensionality b; extensionality f.
    cbn in *; rewrite F_id; cbn; auto.
  }
Qed.
    
Local Obligation Tactic := idtac.

Program Instance Cat_Exponential (C C' : Category) : Exponential C C' :=
{
  exponential := Func_Cat C C';

  eval := Exp_Cat_Eval C C';
  
  Exp_morph_ex := fun C'' F => @Exp_Cat_morph_ex C C' C'' F
}.

Next Obligation. (* Exp_morph_com *)
Proof.
  intros C C' z f.
  match goal with
    [|- ?A = ?B] =>
    cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
  end.
  extensionality x; extensionality y; extensionality h.
  match goal with
    [|- match _ in _ = V return _ with eq_refl => ?A end h = ?B] =>
    transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A h end)
  end.
  destruct W; trivial.
  apply JMeq_eq.
  destruct W; trivial.
  cbn; auto.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
  intros C C' z f u u' H1 H2.
  program_simpl.
  assert (H3 := @f_equal _ _ Exp_Cat_morph_ex _ _ H2).
  repeat rewrite <- Exp_cat_morph_ex_eval_id in H3; trivial.
Qed.

(* Cat_Exponentials defined *)

Program Instance Cat_Has_Exponentials : Has_Exponentials Cat := fun _ _ => _.

Section Exp_Cat_morph_ex_compose.
  Context {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') {B : Category} (G : Functor B C'').

  Theorem Exp_Cat_morph_ex_compose : Exp_Cat_morph_ex (Functor_compose (Prod_Functor G (Functor_id C)) F) = Functor_compose G (Exp_Cat_morph_ex F).
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    {
      extensionality x; extensionality y; extensionality h.
      match goal with
        [|- match _ in _ = V return _ with eq_refl => ?A end h = ?B] =>
        transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A h end)
      end.
      destruct W; trivial.
      apply NatTrans_eq_simplify.
      apply JMeq_eq.
      destruct W; trivial.
    }
    {
      extensionality x.
      match goal with
        [|- ?A = ?B] =>
        set(W := eq_refl : A _o = B _o); apply (Functor_eq_simplify _ _ W)
      end.
      extensionality z; extensionality y; extensionality h.
      cbn.
      rewrite F_id; trivial.
    }
  Qed.

End Exp_Cat_morph_ex_compose.