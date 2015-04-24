Require Import Category.Main.
Require Import Functor.Functor Functor.Representable.Hom_Func.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import NatTrans.Func_Cat.

Section Representable.
  Context {C : Category} (F : Functor C Type_Cat).

  Class Representable : Type :=
    {
      representer : C;
      representation_Iso : F ≡≡ @Fix_Bi_Func_1 C^op _ _ representer (Hom_Func C) ::> Func_Cat _ _
    }.

End Representable.

SubClass CoRepresentable {C : Category} (F : Functor C^op Type_Cat) := @Representable C^op F.