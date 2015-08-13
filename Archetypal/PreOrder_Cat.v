Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.

(** Every pre-order relation is a category. *)
Record PreOrder : Type :=
{
  PreOrder_car :> Type;
  
  PreOrder_rel : PreOrder_car → PreOrder_car → Prop where "a < b" := (PreOrder_rel a b);

  PreOrder_refl : ∀ a, a < a;

  PreOrder_trans : ∀ a b c, a < b → b < c → a < c
}.

Arguments PreOrder_rel {_} _ _.
Arguments PreOrder_refl {_} _.
Arguments PreOrder_trans {_ _ _ _} _ _.

Notation "a < b" := (PreOrder_rel a b) : preorder_scope.

Section PreOrder_Cat.
  Context (P : PreOrder).

  Local Open Scope preorder_scope.

  (* if goal is equality of two preorder relation proofs, we get the to the hypotheses
so that they can be processed by proof irrelevance tactic (PIR). *)
  Local Hint Extern 1 =>
  match goal with
    [|- ?A = ?B :> (_ < _) ] => set A; set B
  end.

  Local Hint Extern 1 => PIR. (* automatically apply proof irrelevance *)
  
  Local Hint Resolve PreOrder_refl PreOrder_trans.

  Local Obligation Tactic := basic_simpl; eauto.

  Program Definition PreOrder_Cat : Category :=
    {|
      Obj := P;
      Hom := fun a b => a < b
    |}
  .

End PreOrder_Cat.