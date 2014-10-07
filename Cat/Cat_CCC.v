Require Import Category.Category.

Require Import Basic_Cons.CCC.

Require Import Cat.Cat.

Require Import Cat.Cat_Terminal.
Require Import Cat.Cat_Product.
Require Import Cat.Cat_Exponential.

Instance Cat_CCC : CCC Cat.
Proof.
  eapply Build_CCC; typeclasses eauto.
Defined.



