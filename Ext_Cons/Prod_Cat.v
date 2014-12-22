Require Import Category.Main.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

(* Product Category *)

Local Obligation Tactic := idtac.

Program Instance Prod_Cat (C C' : Category) : Category :=
{
  Obj := (C * C')%type;

  Hom:= fun a b => ((Hom (fst a) (fst b)) * (Hom (snd a) (snd b))) % type;

  compose := fun _ _ _ f g => (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)));

  id := λ _, (id, id)
}.

Next Obligation.
  intros ? ? [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; cbn in *; repeat rewrite assoc; trivial.
Qed.

Next Obligation.
  intros; rewrite Prod_Cat_obligation_1; reflexivity.
Qed.

Next Obligation.
  program_simpl.
Qed.

Next Obligation.
  program_simpl.
Qed.

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

Program Instance Cat_Proj1 (C C' : Category) : Functor (Prod_Cat C C') C := {FO := fst; FA := fun _ _ f => fst f}.

Next Obligation.
  trivial.
Qed.

Next Obligation.
  trivial.
Qed.

Program Instance Cat_Proj2 (C C' : Category) : Functor (Prod_Cat C C') C' := {FO := snd; FA := fun _ _ f => snd f}.

Next Obligation.
  trivial.
Qed.

Next Obligation.
  trivial.
Qed.

Program Instance Diag_Func (C : Category) : Functor C (Prod_Cat C C) :=
{
  FO := fun a => (a, a);
  FA := fun _ _ f => (f, f)
}.

Next Obligation.
  trivial.
Qed.

Next Obligation.
  trivial.
Qed.

Program Instance Twist_Func (C C' : Category) : Functor (Prod_Cat C C') (Prod_Cat C' C) :=
{
  FO := fun a => (snd a, fst a);
  FA := fun _ _ f => (snd f, fst f)
}.

Next Obligation.
  trivial.
Qed.

Next Obligation.
  trivial.
Qed.
