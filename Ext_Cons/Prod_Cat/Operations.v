Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.

Local Obligation Tactic := idtac.

Program Instance Prod_Functor {C1 C2 C1' C2' : Category} (F : Functor C1 C2) (F' : Functor C1' C2') : Functor (Prod_Cat C1 C1') (Prod_Cat C2 C2') :=
{
  FO := fun a => (F _o (fst a), F' _o (snd a));
  FA := fun _ _ f => (F _a _ _ (fst f), F' _a _ _ (snd f))
}.

Next Obligation.
  intros; cbn; repeat rewrite F_id; trivial.
Qed.

Next Obligation.
  intros; cbn; repeat rewrite F_compose; trivial.
Qed.

Instance Bi_Func_1 {Cx C1 C1' Cy : Category} (F : Functor Cx C1) (F' : Functor (Prod_Cat C1 C1') Cy) : Functor (Prod_Cat Cx C1') Cy :=
  Functor_compose (Prod_Functor F (@Functor_id C1')) F'.

Instance Bi_Func_2 {Cx C1 C1' Cy : Category} (F : Functor Cx C1') (F' : Functor (Prod_Cat C1 C1') Cy) : Functor (Prod_Cat C1 Cx) Cy :=
  Functor_compose (Prod_Functor (@Functor_id C1) F) F'.

Program Instance Fix_Bi_Func_1 {C1 C1' Cy : Category} (x : C1) (F : Functor (Prod_Cat C1 C1') Cy) : Functor C1' Cy :=
{
  FO := fun a => F _o (x, a);
  FA := fun _ _ f => F _a (_, _) (_, _) (@id _ x, f)
}.

Next Obligation.
  intros; cbn; repeat rewrite <- F_id; trivial.
Qed.

Next Obligation.
  intros; cbn; repeat rewrite <- F_compose; simpl; simpl_ids; trivial.
Qed.

Program Instance Fix_Bi_Func_2 {C1 C1' Cy : Category} (x : C1') (F : Functor (Prod_Cat C1 C1') Cy) : Functor C1 Cy :=
{
  FO := fun a => F _o (a, x);
  FA := fun _ _ f => F _a (_, _) (_, _) (f, @id _ x)
}.

Next Obligation.
  intros; cbn; repeat rewrite <- F_id; trivial.
Qed.

Next Obligation.
  intros; cbn; repeat rewrite <- F_compose; simpl; simpl_ids; trivial.
Qed.

Program Instance Diag_Func (C : Category) : Functor C (Prod_Cat C C) :=
{
  FO := fun a => (a, a);
  FA := fun _ _ f => (f, f);
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
}.

Theorem Prod_Functor_Cat_Proj {C D D' : Category} (F : Functor C (Prod_Cat D D')) : Functor_compose (Diag_Func C) (Prod_Functor (Functor_compose F (Cat_Proj1 _ _)) (Functor_compose F (Cat_Proj2 _ _))) = F.
Proof.
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

Program Instance Twist_Func (C C' : Category) : Functor (Prod_Cat C C') (Prod_Cat C' C) :=
{
  FO := fun a => (snd a, fst a);
  FA := fun _ _ f => (snd f, fst f);
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
}.

Section Twist_Prod_Func_Twist.
  Context {C C' : Category} (F : Functor C C') {D D' : Category} (G : Functor D D').

  Theorem Twist_Prod_Func_Twist : Functor_compose (Twist_Func _ _) (Functor_compose (Prod_Functor F G) (Twist_Func _ _)) = Prod_Functor G F.
  Proof.  
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

End Twist_Prod_Func_Twist.
  
Instance ProdOp_Prod_of_Op (C D : Category) : Functor (Prod_Cat C D)^op (Prod_Cat C^op D^op) :=
{
  FO := fun x => x;
  FA := fun _ _ x => x;
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
}.

Instance Prod_of_Op_ProdOp (C D : Category) : Functor (Prod_Cat C^op D^op) (Prod_Cat C D)^op :=
{
  FO := fun x => x;
  FA := fun _ _ x => x;
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
}.

Program Instance Opposite_Prod (C D : Category) : (Prod_Cat C D)^op ≡≡ Prod_Cat C^op D^op ::> Cat :=
  Build_Isomorphism _ _ _ (ProdOp_Prod_of_Op _ _) (Prod_of_Op_ProdOp _ _) eq_refl eq_refl.


Section Prod_Functor_compose.
  Context {C D E: Category} (F : Functor C D) (G : Functor D E)
          {C' D' E': Category} (F' : Functor C' D') (G' : Functor D' E').

  Theorem Prod_Functor_compose : Functor_compose (Prod_Functor F F') (Prod_Functor G G') = Prod_Functor (Functor_compose F G) (Functor_compose F' G').
  Proof.
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
                                   
End Prod_Functor_compose.