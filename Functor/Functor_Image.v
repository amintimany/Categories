Require Import Category.Core.
Require Import Functor.Functor.

Inductive Composable_Chain `(C : Category Obj Hom) (a b : Obj) : Type :=
| Single : Hom a b → Composable_Chain C a b
| Chain : ∀ (c : Obj), Hom a c → Composable_Chain C c b → Composable_Chain C a b
.

Fixpoint Forall_Links `(C : Category Obj Hom) (a b : Obj) (ch : Composable_Chain C a b) (P : ∀ (x y : Obj), Hom x y → Prop) : Prop :=
  match ch with
    | Single f => P _ _ f
    | Chain _ f ch' => P _ _ f ∧ Forall_Links C _ _ ch' P
  end.

Fixpoint Compose_of `(C : Category Obj Hom) (a b : Obj) (ch : Composable_Chain C a b) : Hom a b :=
  match ch with
    | Single f => f
    | Chain _ f ch' => (Compose_of C _ _ ch') ∘ f
  end.

Fixpoint Chain_Compose `(C : Category Obj Hom) (a b c : Obj) (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) : Composable_Chain C a c :=
  match ch1 with
    | Single f => Chain _ _ _ _ f ch2
    | Chain _ f ch' => Chain _ _ _ _ f (Chain_Compose C _ _ _ ch' ch2)
  end.

Theorem Compose_of_Chain_Compose `(C : Category Obj Hom) (a b c : Obj) (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) : (Compose_of _ _ _ ch2)∘ (Compose_of _ _ _ ch1) = Compose_of _ _ _ (Chain_Compose _ _ _ _ ch1 ch2).
Proof.
  induction ch1; auto.
  simpl.
  rewrite <- assoc.
  rewrite IHch1; trivial.
Qed.

Theorem Forall_Links_Chain_Compose `(C : Category Obj Hom) (a b c : Obj) (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c) (P : ∀ (x y : Obj), Hom x y → Prop) : Forall_Links _ _ _ ch1 P → Forall_Links _ _ _ ch2 P → Forall_Links _ _ _ (Chain_Compose _ _ _ _ ch1 ch2) P.
Proof.
  intros H1 H2.
  induction ch1.
  simpl in *; auto.
  destruct H1 as [H11 H12].
  simpl in *; split; auto.
Qed.

Section Functor_Image.
  Context `{C : Category Obj Hom}
          `{D : Category Obj' Hom'}
          (F : Functor C D).

  Program Definition Functor_Image :=
    SubCategory D
                (λ a, ∃ x, F _o x = a)
                (
                  λ a b f,
                  ∃ (ch : Composable_Chain D a b),
                    (Compose_of _ _ _ ch) = f
                    ∧
                    Forall_Links _ _ _ ch (
                      λ x y g,
                      ∃ (c d : Obj) (h : Hom c d)
                        (Fca : F _o c = x) (Fdb : F _o d = y),
                        match Fca in (_ = Z) return Hom' Z _ with
                            eq_refl =>
                            match Fdb in (_ = Y) return Hom' _ Y with
                                eq_refl => F _a _ _ h
                            end
                        end = g)
                )
                _ _.
  
  Next Obligation. (* Hom_Cri_id *)
  Proof.
    exists (Single _ _ _ (F _a _ _ id)); simpl; split; auto.
    do 3 eexists; do 2 exists eq_refl; reflexivity.
  Qed.

  Next Obligation. (* Hom_Cri_compose *)
  Proof.
    match goal with
        [ch1 : Composable_Chain _ ?a ?b, ch2 : Composable_Chain _ ?b ?c|- _] =>
        exists (Chain_Compose _ _ _ _ ch1 ch2); split
               end.
               rewrite <- Compose_of_Chain_Compose; trivial.
               apply Forall_Links_Chain_Compose; auto.
  Qed.

End Functor_Image.