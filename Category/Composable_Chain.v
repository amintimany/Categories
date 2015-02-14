Require Import Category.Category.

Inductive Composable_Chain (C : Category) (a b : C) : Type :=
| Single : Hom a b → Composable_Chain C a b
| Chain : ∀ (c : Obj), Hom a c → Composable_Chain C c b → Composable_Chain C a b
.

Arguments Single {_ _ _} _.
Arguments Chain {_ _ _ _} _ _.

Fixpoint Forall_Links {C : Category} {a b : C} (ch : Composable_Chain C a b) (P : ∀ {x y : Obj}, Hom x y → Prop) : Prop :=
  match ch with
    | Single f => P f
    | Chain f ch' => P f ∧ Forall_Links ch' (@P)
  end.

Fixpoint Compose_of {C : Category} {a b : C} (ch : Composable_Chain C a b) {struct ch} : Hom a b :=
  match ch with
    | Single f => f
    | Chain f ch' => (Compose_of ch') ∘ f
  end.

Fixpoint Chain_Compose {C : Category} {a b c : C} (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) : Composable_Chain C a c :=
  match ch1 with
    | Single f => Chain f ch2
    | Chain f ch' => Chain f (Chain_Compose ch' ch2)
  end.

Theorem Compose_of_Chain_Compose (C : Category) (a b c : C) (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) : (Compose_of ch2)∘ (Compose_of ch1) = Compose_of (Chain_Compose ch1 ch2).
Proof.
  induction ch1; auto.
  simpl.
  rewrite <- assoc.
  rewrite IHch1; trivial.
Qed.

Theorem Forall_Links_Chain_Compose (C : Category) (a b c : C) (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) (P : ∀ (x y : Obj), Hom x y → Prop) : Forall_Links ch1 P → Forall_Links ch2 P → Forall_Links (Chain_Compose ch1 ch2) P.
Proof.
  intros H1 H2.
  induction ch1.
  simpl in *; auto.
  destruct H1 as [H11 H12].
  simpl in *; split; auto.
Qed.



