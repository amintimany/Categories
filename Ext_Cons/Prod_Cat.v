Require Import Category.Main.


Set Primitive Projections.

Set Universe Polymorphism.

(* Product Category *)

Program Instance Prod_Cat (C C' : Category) : Category :=
{
  Obj := (@Obj C * @Obj C')%type;

  Hom:= (λ a b, ((Hom (fst a) (fst b)) * (Hom (snd a) (snd b))) % type);

  compose := λ _ _ _ f g, (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)));

  id := λ _, (id, id)
}.

(* Prod_Cat defined *)
