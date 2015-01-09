Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Class Card_Restriction : Type :=
{
  Card_Rest : Type → Prop;
  
  Card_Rest_Respect : ∀ (A B : Type), A ≡ B → Card_Rest A → Card_Rest B
}.

Coercion Card_Rest : Card_Restriction >-> Funclass.
