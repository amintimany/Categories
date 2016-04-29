Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Cat.Product.

(** The exponential in cat is jsut the functor category. *)

Local Open Scope functor_scope. 

(** Evaluation functor. *)
Program Definition Exp_Cat_Eval (C C' : Category) :
  ((Func_Cat C C') × C) –≻ C' :=
{|
  FO := fun x => ((fst x) _o (snd x))%object;
  FA := fun A B f => (((fst B) _a (snd f)) ∘ (@Trans _ _ _ _ (fst f) _))%morphism
|}.

Next Obligation. (* F_compose *)
Proof.
  repeat rewrite F_compose.
  repeat rewrite assoc.
  match goal with
      [|- (?A ∘ ?B = ?A ∘ ?C)%morphism] => cutrewrite (B = C); trivial
  end.
  repeat rewrite assoc_sym.
  match goal with
      [|- (?A ∘ ?B = ?C ∘ ?B)%morphism] => cutrewrite (A = C); trivial
  end.
  rewrite Trans_com; trivial.
Qed.

(* Exp_Cat_Eval defined *)

(** The arrow map of curry functor. *)
Program Definition Exp_Cat_morph_ex_A
        {C C' C'' : Category} (F : (C'' × C) –≻  C')
        (a b : C'') (h : (a –≻ b)%morphism)
  :
    ((Fix_Bi_Func_1 a F) –≻ (Fix_Bi_Func_1 b F))%nattrans :=
{|
  Trans := fun c => (F _a (h, id _ c))%morphism
|}.

(* Exp_Cat_morph_ex_A defined *)

Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

(** The curry functor. *)
Program Definition Exp_Cat_morph_ex
        {C C' C'' : Category}
        (F : (C'' × C) –≻ C')
  :
    C'' –≻ (Func_Cat C C') :=
{|
  FO := fun a => Fix_Bi_Func_1 a F;
  FA := Exp_Cat_morph_ex_A F
|}.

(** Proof that currying after uncurrying gives back the same functor. *)
Lemma Exp_cat_morph_ex_eval_id
      {C C' C'' : Category}
      (u : C'' –≻ (Func_Cat C C'))
  :
    (u =
     Exp_Cat_morph_ex
       (
         (Exp_Cat_Eval C C')
           ∘ ((×ᶠⁿᶜ _ Cat_Has_Products) @_a (_, _) (_, _) (u, id Cat C))
       )
    )%morphism.
Proof.
  Func_eq_simpl.
  {
    extensionality a; extensionality b; extensionality h; cbn.
    apply NatTrans_eq_simplify.
    extensionality m.
    apply JMeq_eq.
    apply (@JMeq_trans _ _ _ _ (Trans (u _a h)%morphism m)).
    + match goal with [H : _ = _ |-_] => destruct H end; trivial.
    + cbn; auto.
  }
  {
    FunExt; cbn.
    Func_eq_simpl; FunExt; cbn.
    auto.
  }
Qed.

(** The exponential for category of categories (functor categories). *)
Program Definition Cat_Exponential (C C' : Cat) : (C ⇑ C')%object :=
{|
  exponential := Func_Cat C C';

  eval := Exp_Cat_Eval C C';
  
  Exp_morph_ex := fun C'' F => @Exp_Cat_morph_ex C C' C'' F
|}.

Next Obligation. (* Exp_morph_com *)
Proof.
  Func_eq_simpl.
  FunExt; cbn.
  rewrite <- F_compose; cbn.
  auto.
Qed.

Local Obligation Tactic := idtac.

Next Obligation. (* Exp_morph_unique *)
Proof.  
  intros C C' z f u u' H1 H2.
  rewrite H1 in H2; clear H1.
  assert (H3 := @f_equal _ _ Exp_Cat_morph_ex _ _ H2).
  repeat rewrite <- Exp_cat_morph_ex_eval_id in H3; trivial.
Qed.

(* Cat_Exponentials defined *)

Program Instance Cat_Has_Exponentials : Has_Exponentials Cat := Cat_Exponential.