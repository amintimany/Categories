Require Import Coq.Logic.JMeq.

Notation "a ≃ b" := (JMeq a b) (at level 70, right associativity).


Require Export Coq.Unicode.Utf8.

Reserved Notation "f ∘ g" (at level 11, right associativity).

Reserved Notation "a ≫–> b" (at level 10, no associativity).

Reserved Notation "a –≫ b" (at level 10, no associativity).

Reserved Notation "F '_o'" (at level 10, no associativity).

Reserved Notation "F '_a'" (at level 10, no associativity).

Reserved Notation "F ⊣ G" (at level 12, no associativity).

Delimit Scope category_scope with category.

Delimit Scope morphism_scope with morphism.

Delimit Scope object_scope with object.

Delimit Scope functor_scope with functor.

Open Scope category_scope.

Open Scope morphism_scope.

Open Scope object_scope.

Open Scope functor_scope.