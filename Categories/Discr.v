Require Import Category.Main.
Require Import Essentials.Empty.
Require Import Functor.Functor.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Type_Cat.

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

  Program Instance Discr_Cat : Category Obj Discr_Hom :=
    {
      compose := Discr_Hom_compose;
      id := λ a, Discr_id a
    }.

End Discr.

Hint Extern 1 =>
  match goal with
      [H : Discr_Hom _ _ _ |- _] => destruct H
  end.

Notation "0" := (Discr_Cat Empty) : category_scope.
Notation "1" := (Discr_Cat unit) : category_scope.

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
  Context `(C : Category Obj Hom) (A : Type) (Omap : A → Obj).

  Program Instance Discrete_Functor : Functor (Discr_Cat A) C :=
    {
      FO := Omap;
      
      FA := λ (a b : A) (X : Discr_Hom A a b),
            match X in (Discr_Hom _ y y0) return (Hom (Omap y) (Omap y0)) with
              | Discr_id _ => id
            end
    }.

End Discr_Func.

(* The fact that in discrete category object type and arrow type are isomorphic *)
Instance Discr_Hom_Iso (A : Type) : A ≡ Arrow (Discr_Cat A).
Proof.
  exists (λ a, (Build_Arrow _ _ _ _ _ (Discr_id _ a))).
  exists (λ x, Orig x); extensionality x; [|destruct x as [? ? []]]; simpl; trivial.
Qed.