Global Set Primitive Projections.

Global Set Universe Polymorphism.

Inductive Empty : Set :=.

Hint Extern 1 =>
let tac := (repeat intros ?); match goal with [H : Empty |- _] => contradict H end in
match goal with
  | [|- context[Empty]] => tac
  | [H : context[Empty] |- _] => tac
end
.

Class prod (A B : Type) := {fst : A; snd : B}.

Arguments fst {_ _ } _.
Arguments snd {_ _ } _.
Arguments Build_prod {_ _ } _ _.

Notation "( X , Y )" := (Build_prod X Y).
Notation "X * Y" := (prod X Y) : type_scope.
