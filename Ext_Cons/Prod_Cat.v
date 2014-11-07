Require Import Category.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Product Category *)

Local Obligation Tactic := idtac.

Program Instance Prod_Cat (C C' : Category) : Category :=
{
  Obj := (@Obj C * @Obj C')%type;

  Hom:= (λ a b, ((Hom (fst a) (fst b)) * (Hom (snd a) (snd b))) % type);

  compose := λ _ _ _ f g, (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)));

  id := λ _, (id, id)
}.

Next Obligation.
  intros ? ? [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *; repeat rewrite assoc; trivial.
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

(* Prod_Cat defined *)
