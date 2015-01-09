Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.

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

Theorem Prod_compose_id (C D : Category) (a b c : C) (d : D) (f : Hom a b) (g : Hom b c) : (g ∘ f, @id _ d) = @compose (Prod_Cat _ _) (_, _) (_, _) (_, _) (f, @id _ d) (g, @id _ d).
Proof.
  cbn; auto.
Qed.

Theorem Prod_id_compose (C D : Category) (a : C) (b c d : D) (f : Hom b c) (g : Hom c d) : (@id _ a, g ∘ f) = @compose (Prod_Cat _ _) (_, _) (_, _) (_, _) (@id _ a, f) (@id _ a, g).
Proof.
  cbn; auto.
Qed.

Theorem Prod_cross_compose (C D : Category) (a b : C) (c d : D) (f : Hom a b) (g : Hom c d) : @compose (Prod_Cat _ _) (_, _) (_, _) (_, _) (@id _ a, g) (f, @id _ d) = @compose (Prod_Cat _ _) (_, _) (_, _) (_, _) (f, @id _ c) (@id _ b, g).
Proof.
  cbn; auto.
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
