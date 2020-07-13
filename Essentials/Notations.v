From Coq.Unicode Require Export Utf8.

Reserved Notation "C '^op'" (at level 50, no associativity).

Reserved Notation "a --> b" (at level 90, b at level 200, right associativity).

Reserved Notation "f '⁻¹'" (at level 50, no associativity).

Reserved Notation "a ≃ b" (at level 70, no associativity).

Reserved Notation "a ≃≃ b ::> C" (at level 70, no associativity).

Reserved Notation "f ∘ g" (at level 51, right associativity).

Reserved Notation "f '∘_h' g" (at level 51, right associativity).

Reserved Notation "a ≫–> b" (at level 100, no associativity).

Reserved Notation "a –≫ b" (at level 100, no associativity).

Reserved Notation "F '_o'" (at level 50, no associativity).

Reserved Notation "F '_a'" (at level 50, no associativity).

Reserved Notation "F '@_a'" (at level 50, no associativity).

Reserved Notation "F ⊣ G" (at level 100, no associativity).

Reserved Notation "F ⊣_hom G" (at level 100, no associativity).

Reserved Notation "F ⊣_ucu G" (at level 100, no associativity).

Reserved Notation "a × b" (at level 80, no associativity).

Reserved Notation "a ⇑ b" (at level 79, no associativity).

Reserved Notation "'Π' m" (at level 50, no associativity).

Reserved Notation "'Σ' m" (at level 50, no associativity).

Reserved Notation "'Π_' C ↓ m" (at level 50, no associativity).

Reserved Notation "'Σ_' C ↓ m" (at level 50, no associativity).

Declare Scope category_scope.
Delimit Scope category_scope with category.

Declare Scope morphism_scope.
Delimit Scope morphism_scope with morphism.

Declare Scope object_scope.
Delimit Scope object_scope with object.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.

Declare Scope nattrans_scope.
Delimit Scope nattrans_scope with nattrans.

Declare Scope natiso_scope.
Delimit Scope natiso_scope with natiso.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.

Declare Scope preorder_scope.
Delimit Scope preorder_scope with preorder.
