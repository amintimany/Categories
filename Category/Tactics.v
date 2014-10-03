Require Import Category.Category.

Obligation Tactic := program_simpl; auto.

(* basic tactics for categories *)

Ltac reveal_comp_in_goal f g :=
  match goal with
    | [ |- context[f ∘ g] ] => idtac
    | [ |- context[?B ∘ (?A ∘ f)] ] =>
      let J := fresh "H" in
      assert (J := assoc f A B); rewrite <- J; clear J
    | [ |- context[((g ∘ ?A) ∘ ?B)] ] =>
      let J := fresh "H" in
      assert (J := assoc B A g); rewrite J; clear J
    | [ |- context[(?A ∘ f) ∘ (g ∘ ?B)] ] =>
      let J := fresh "H" in
      assert (J := assoc B g (A ∘ f)); rewrite <- J; clear J
    | [ |- context[((?A ∘ f) ∘ g)] ] =>
      let J := fresh "H" in
      assert (J := assoc g f A); rewrite J; clear J
    | [ |- context[(f ∘ (g ∘ ?B))] ] =>
      let J := fresh "H" in
      assert (J := assoc B g f); rewrite <- J; clear J
  end;
  match goal with
    | [ |- context[f ∘ g] ] => idtac
    | _ => reveal_comp_in_goal f g
  end
.

Ltac reveal_comp_in_I f g I :=
  match type of I with
    | context[f ∘ g] => idtac
    | context[?B ∘ (?A ∘ f)] =>
      let J := fresh "H" in
      assert (J := assoc f A B); rewrite <- J in I; clear J
    | context[((g ∘ ?A) ∘ ?B)] =>
      let J := fresh "H" in
      assert (J := assoc B A g); rewrite J in I; clear J
    | context[(?A ∘ f) ∘ (g ∘ ?B)] =>
      let J := fresh "H" in
      assert (J := assoc B g (A ∘ f)); rewrite <- J in I; clear J
    | context[((?A ∘ f) ∘ g)] =>
      let J := fresh "H" in
      assert (J := assoc g f A); rewrite J in I; clear J
    | context[(f ∘ (g ∘ ?B))] =>
      let J := fresh "H" in
      assert (J := assoc B g f); rewrite <- J in I; clear J
  end;
  match type of I with
    | context[f ∘ g] => idtac
    | _ => reveal_comp_in_I f g
  end
.

Tactic Notation "reveal_comp" constr(f) constr(g) := reveal_comp_in_goal f g.

Tactic Notation "reveal_comp" constr(f) constr(g) "in" hyp(I) := reveal_comp_in_I f g I.

Ltac simpl_ids :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J; clear J | trivial]
  in
  repeat(
      match goal with
        | [|- context[?A ∘ id] ] => rewrite id_unit_right
        | [|- context[id ∘ ?A] ] => rewrite id_unit_left
        | [|- ?A ∘ ?B = ?A] => id_detected B
        | [|- ?A = ?A ∘ ?B] => id_detected B
        | [|- ?B ∘ ?A = ?A] => id_detected B
        | [|- ?A = ?B ∘ ?A] => id_detected B
      end
    )
.

Ltac simpl_ids_in_I I :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J in I; clear J | trivial]
  in
  repeat(
      match type of I with
        | context[?A ∘ id] => rewrite id_unit_right in I
        | context[id ∘ ?A] => rewrite id_unit_left in I
        | ?A ∘ ?B = ?A => id_detected B
        | ?A = ?A ∘ ?B => id_detected B
        | ?B ∘ ?A = ?A => id_detected B
        | ?A = ?B ∘ ?A => id_detected B
      end
    )
.

Tactic Notation "simpl_ids" := simpl_ids.

Tactic Notation "simpl_ids" "in" hyp(I) := simpl_ids_in_I I.

Hint Extern 2 => simpl_ids.

(* Automating use of functional_extensionality *)
Hint Extern 1 => 
match goal with
    [|- ?A = ?B :> (?C -> ?D)] =>
      let x := fresh "x" in
      extensionality x
end.

Hint Extern 3 =>
match goal with
    [|- ?A = ?B :> ?Hom _ _] =>
    repeat rewrite assoc; trivial; fail
end.




