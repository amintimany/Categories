Require Import Category.Main.

(* The category of Types (Coq's "Type")*)

Program Instance Type_Cat : Category :=
{
  Obj := Type;

  Hom := λ A B, A → B;

  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);

  id := fun A => fun x => x

}.


