Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Class Card_Restriction : Type :=
{
  Card_Rest : Type → Prop;
  
  Card_Rest_Respect : ∀ (A B : Type), A ≡ B → Card_Rest A → Card_Rest B
}.

Coercion Card_Rest : Card_Restriction >-> Funclass.

Program Definition Finite : Card_Restriction :=
  {|
    Card_Rest := fun A => inhabited {n : nat & A ≡≡ {x : nat | x < n} ::> Type_Cat}
  |}.

Next Obligation.
Proof.
  destruct H as [[n I]].
  eexists.
  refine (existT _ n (Isomorphism_Compose (Inverse_Isomorphism X) I)).
Qed.