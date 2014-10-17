Require Import Category.Main.

(* Product Category *)

Program Instance Prod_Cat `(C : Category Obj Hom) `(C' : Category Obj' Hom') : Category (Obj * Obj')%type (λ a b, ((Hom (fst a) (fst b)) * (Hom' (snd a) (snd b))) % type) :=
{
  compose := λ _ _ _ f g, (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)));

  id := λ _, (id, id)
}.

(* Prod_Cat defined *)
