Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Representable.Hom_Func.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Coq_Cats.Type_Cat.Type_Cat_CCC.
Require Import Ext_Cons.Prod_Cat.
Require Import NatTrans.NatTrans.
Require Import Basic_Cons.CCC.
Require Import Cat.Cat_CCC.

Require Import Yoneda.Y_emb.

Set Primitive Projections.

Set Universe Polymorphism.

Section Lifting.
  Universe i j.

  Let i_le_j := Type@{i} : Type@{j}.
  
  Definition Lift (A : Type@{i}) : Type@{j} := A.
  
End Lifting.

Section Yoneda_Hom_Func.

  Universe i j k l m n
           CHE1 CHE2 CHE3 CHE4 CHE5 CHE6 CHE7 CHE8 CHE9 CHE10
           CHE11 CHE12 CHE13 CHE14 CHE15 CHE16 CHE17 CHE18 CHE19 CHE20
           CHE21 CHE22 CHE23 CHE24 CHE25 CHE26 CHE27 CHE28 CHE29 CHE30
           CHE31 CHE32 CHE33 CHE34 CHE35 CHE36 CHE37 CHE38 CHE39 CHE40
           CHE41 CHE42 CHE43 CHE44 CHE45 CHE46 CHE47 CHE48 CHE49 CHE50.

  Context {C : Category@{i j}}.

  Set Printing Universes.
  
  Set Printing All.

  Definition SD : @Obj Cat := Type_Cat.
  
  Print Lift.

  Print Type_Cat.Type_Cat_obligation_1.

  Print C.

  Check (Hom_Func C).

  Let S : @Hom Cat@{k l m n} _ _ := (Hom_Func C).

  Print Hom_Func.

  Print Has_Exponentials.

  Definition CAT_Has_Products : Has_Products Cat@{k l m n} := Cat_Has_Products.

  Definition CAT_Has_Exponentials : @Has_Exponentials Cat@{k l m n} CAT_Has_Products.
  Proof.
    assert (H := Cat_Has_Exponentials).
    unfold CAT_Has_Products.
    


      

  Check (@curry Cat@{k l m n} Cat_Has_Products CAT_Has_Exponentials _ _ _ (Hom_Func C)).
  
  Check Cat_Has_Exponentials.
  
  Print Cat_CCC.
  
  Theorem Yoneda_Hom_Func : @curry Cat _ Cat_Has_Exponentials _ _ _ (Hom_Func C^op) = Yoneda_emb C.

  Check (@curry Cat _ _ _ _ _ (Hom_Func C)).


  Print Hom_Func.


Print Yoneda_emb.

