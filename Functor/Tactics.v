Require Import Category.Main.
Require Import Functor.Functor.

Set Primitive Projections.

Set Universe Polymorphism.

Ltac Functor_Simplify :=
  match goal with
    | [|- ?F _a _ _ ?A = @id _ _ _ (?F _o ?x)] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- (@id _ _ _ (?F _o ?x)) = ?F _a _ _ ?A] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C ∘ ?F _a _ _ ?D] =>
      repeat rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?C = ?F _a _ _ ?A ∘ ?F _a _ _ ?B] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- context [?F _a _ _ id] ] =>
      rewrite F_id; (simpl||idtac)
    | [|- context [?F _a _ _ ?A ∘ ?F _a _ _ ?B]] =>
      rewrite <- F_compose; (simpl||idtac)
  end
.

Hint Extern 2 => Functor_Simplify.

Tactic Notation "FA_extensionality" ident(x) ident(y) ident(h) :=
  apply FA_extensionality; [trivial|intros x y h]
.

Tactic Notation "Functor_extensionality" ident(x) ident(y) ident(h) :=
  apply Functor_extensionality; [intros x|intros x y h]
.

Hint Extern 1 =>
  match goal with
      [|- ?F = ?G :> (Functor _ _)] =>
      let x := fresh "x" in
      let y := fresh "y" in
      let f := fresh "f" in
      Functor_extensionality x y f
  end
.
