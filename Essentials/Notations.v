Require Import Coq.Logic.JMeq.

Require Export Coq.Unicode.Utf8.

Reserved Notation "f ∘ g" (at level 11, right associativity).

Reserved Notation "a ≫–> b" (at level 10, no associativity).

Reserved Notation "a –≫ b" (at level 10, no associativity).

Reserved Notation "F '_o'" (at level 10, no associativity).

Reserved Notation "F '_a'" (at level 10, no associativity).

Reserved Notation "'_I_' D" (at level 9, no associativity).
Reserved Notation "'_T_' D" (at level 9, no associativity).

Reserved Notation "x × y" (at level 9, no associativity).
Reserved Notation "≪ f , g ≫" (at level 9, no associativity).
Reserved Notation "f ⊕ g" (at level 9, no associativity).
Reserved Notation "〚 x , y 〛" (at level 9, no associativity).

Reserved Notation "x ↑ y" (at level 9, no associativity).

Reserved Notation "f ↑↑ g " (at level 9, no associativity).



Notation "a ≃ b" := (JMeq a b) (at level 70, right associativity).