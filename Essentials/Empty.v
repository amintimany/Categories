Inductive Empty : Type :=.

Hint Extern 1 =>
let tac := (repeat intros ?); match goal with [H : Empty |- _] => contradict H end in
match goal with
  | [|- context[Empty]] => tac
  | [H : context[Empty] |- _] => tac
end
.
