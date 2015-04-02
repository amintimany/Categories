Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Representable.Hom_Func.

Section Hom_Func_Twist.
  Context (C : Category).
  
  Theorem Hom_Func_Twist : (Hom_Func C^op) = Functor_compose (Twist_Func C C^op) (Hom_Func C).
  Proof.
    Functor_extensionality c c' f.
    trivial.
    cbn; auto.
  Qed.

End Hom_Func_Twist.
