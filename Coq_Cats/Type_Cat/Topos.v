Require Import Category.Main.
Require Import Topos.Topos.
Require Import Limits.Limit.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Coq_Cats.Type_Cat.CCC.
Require Import Coq_Cats.Type_Cat.Complete.
Require Import Coq_Cats.Type_Cat.SubObject_Classifier. 

Instance Type_Cat_Topos : Topos :=
  {
    Topos_Cat := Type_Cat;
    Topos_Cat_CCC := Type_Cat_CCC;
    Topos_Cat_SOC := Type_Cat_SubObject_Classifier;
    Topos_Cat_Fin_Limit := Complete_Has_Restricted_Limits Type_Cat Finite
  }.