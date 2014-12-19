Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.

Set Primitive Projections.

Set Universe Polymorphism.

Program Instance Exp_Func {C : Category}
        {hp : Has_Products C}
        (exps : ∀ a b, Exponential a b)
: Functor (Prod_Cat (C^op) C) C :=
{
  FO := fun x => exps (fst x) (snd x);
  FA := fun a b f => 
           Exp_morph_ex _ ((snd f) ∘ eval ∘ ((@Prod_Func C _) _a (_, fst b) (_, fst a) (@id _ (exps (fst a) (snd a)), fst f)))
}.

Next Obligation. (* F_id *)
Proof.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com.
  reflexivity.
  simpl; simpl_ids; reflexivity.
Qed.

Local Obligation Tactic := idtac.
Next Obligation. (* F_compose *)
Proof.
  intros.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com; reflexivity.
  match goal with
        [|- _ = _ ∘ ?U _a _ _ (?W, ?C)] =>
        match W with
            ?A ∘ ?B =>
            let H := fresh "H" in
            cutrewrite (U _a (_, _) (_, _) (W, C) = (U _a (_, _) (_, _) (A, C)) ∘ (U _a (_, _) (_, _) (B, C)))
        end
    end.
  {
    rewrite <- (@assoc _ _ _ _ _ _ _ eval).
    rewrite <- Exp_morph_com.
    repeat rewrite assoc.
    match goal with
      [|- _ = _ ∘ ?A ∘ ?M] =>
      match M with
          ?B ∘ ?D =>
          match B with
              (Prod_Func _a (_, _) (_, _) (id, ?E)) =>
              match type of E with
                  Hom ?G ?H =>
                  match D with
                      (Prod_Func _a (_, _) (_, _) ( ?F, id)) =>
                      match type of F with
                          Hom ?I ?J =>
                          cutrewrite (M = (Prod_Func _a (_, _) (_, _) (F, id)) ∘ (Prod_Func _a (_, _) (_, _) (@id _ I, E)))
                      end
                  end
              end
          end
      end
    end.
    {
      match goal with
          [|- _ = _ ∘ ?A ∘ ?B ∘ ?C] =>
          reveal_comp A B
      end.
      rewrite <- Exp_morph_com.
      repeat rewrite assoc.
      rewrite <- F_compose.
      simpl; auto.
    }
    {
      repeat rewrite <- F_compose.
      simpl; simpl_ids; trivial.
    }
  }
  {
    rewrite <- F_compose.
    simpl; auto.
  }
Qed.

(* Exponential_Functor defined *)
