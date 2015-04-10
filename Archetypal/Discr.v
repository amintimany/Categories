Require Import Category.Main.
Require Import Functor.Functor.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Type_Cat.

(* empty and singleton categories *)

Instance EmptyCat : Category :=
  {
    Obj := Empty;
    Hom := fun _ _ => Empty;
    compose := fun _ _ _ _ _ => Empty_rect _ _;
    assoc := fun _ _ _ _ _ _ _ => eq_refl;
    assoc_sym := fun _ _ _ _ _ _ _ => eq_refl;
    id := fun _ => Empty_rect _ _;
    id_unit_left := fun _ _ h => Empty_rect _ _;
    id_unit_right := fun _ _ h => Empty_rect _ _
  }.

Instance SingletonCat : Category :=
  {
    Obj := unit;
    Hom := fun _ _ => unit;
    compose := fun _ _ _ _ _ => tt;
    assoc := fun _ _ _ _ _ _ _ => eq_refl;
    assoc_sym := fun _ _ _ _ _ _ _ => eq_refl;
    id := fun _ => tt;
    id_unit_left :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => eq_refl
        end;
    id_unit_right :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => eq_refl
        end
  }.

  
Notation "0" := (EmptyCat) : category_scope.
Notation "1" := (SingletonCat) : category_scope.


(* discrete categories in general *)

Section Discr.
  Context (Obj : Type).

  Inductive Discr_Hom : Obj → Obj → Type :=
    Discr_id : ∀ (x : Obj), Discr_Hom x x
  .

  Hint Constructors Discr_Hom.

  Hint Extern 1 =>
  match goal with
      [H : Discr_Hom _ _ |- _] => destruct H
  end.

  Definition Discr_Hom_compose (a b c : Obj) (f : Discr_Hom a b) (g : Discr_Hom b c) : Discr_Hom a c.
  Proof.
    auto.
  Defined.

  Program Instance Discr_Cat : Category :=
    {
      Obj := Obj;
      Hom := Discr_Hom;
      compose := Discr_Hom_compose;
      id := fun a => Discr_id a
    }.

End Discr.

Hint Extern 1 =>
  match goal with
      [H : Discr_Hom _ _ _ |- _] => destruct H
  end.

Inductive S_Type (T : Type) : Type :=
| NEW : unit → S_Type T
| OLD : T → S_Type T
.

Fixpoint Type_n (n : nat) {struct n} : Type :=
  match n with
    | O => Empty
    | S O => unit
    | S n' => S_Type (Type_n n')
  end
.

Notation "'Discr_n' n" := (Discr_Cat (Type_n n)) (at level 200, n bigint) : category_scope.

(* Discrete Functor *)
Section Discr_Func.
  Context (C : Category) {A : Type} (Omap : A → C).

  Program Instance Discrete_Functor : Functor (Discr_Cat A) C :=
    {
      FO := Omap;
      
      FA := fun (a b : A) (X : Discr_Hom A a b) =>
            match X in (Discr_Hom _ y y0) return (Hom (Omap y) (Omap y0)) with
              | Discr_id _ _ => id
            end
    }.

End Discr_Func.

Local Hint Extern 1 => let z := fresh in extensionality z.
Local Hint Extern 1 => match goal with [z : Arrow (Discr_Cat _) |- _] => destruct z as [? ? []] end.

(* The fact that in discrete category object type and arrow type are isomorphic *)
Instance Discr_Hom_Iso (A : Type) : A ≡≡ Arrow (Discr_Cat A) ::> Type_Cat.
Proof.
  eapply (Build_Isomorphism Type_Cat _ _ (λ a, (Build_Arrow (Discr_Cat A) _ _ (Discr_id A a))) (λ a : (Arrow (Discr_Cat _)), Orig a)); auto.
Qed.