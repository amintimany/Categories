Global Set Primitive Projections.

Global Set Universe Polymorphism.

Global Unset Universe Minimization ToSet.

Global Set Warnings "-notation-overridden".

(** The Empty Type. *)
Inductive Empty : Type :=.

Hint Extern 1 =>
let tac :=
    (repeat intros ?); match goal with [H : Empty |- _] => contradict H end
in
match goal with
| [|- context[Empty]] => tac
| [H : context[Empty] |- _] => tac
end : core.

(** The product type, defined as a record to enjoy eta rule for records. *)
Record prod (A B : Type) := pair {fst : A; snd : B}.

Arguments fst {_ _} _.
Arguments snd {_ _} _.
Arguments pair {_ _} _ _.

Notation "( x , y )" := (pair x y).
Notation "x * y" := (prod x y) : type_scope.

Add Printing Let prod.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Register prod as core.prod.type.
Register pair as core.prod.intro.
Register prod_rect as core.prod.rect.
