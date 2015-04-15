Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.

(* Product Category *)

Local Obligation Tactic := idtac.

Program Instance Prod_Cat (C C' : Category) : Category :=
{
  Obj := C * C';
              
  Hom := fun a b => ((Hom (fst a) (fst b)) * (Hom (snd a) (snd b)))%type;

  compose := fun a b c f g => (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)));

  id := fun c => (id, id)
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