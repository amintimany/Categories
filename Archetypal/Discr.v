Require Import Category.Main.
Require Import Functor.Functor.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import NatTrans.

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

  Program Instance Discr_Cat : Category :=
    {
      Obj := Obj;
      Hom := fun a b => a = b;
      compose := @eq_trans _;
      id := fun a => eq_refl
    }.

End Discr.

Definition Type_n (n : nat) : Type := {x : nat| x < n}.

Notation "'Discr_n' n" := (Discr_Cat (Type_n n)) (at level 200, n bigint) : category_scope.

(* Discrete Functor *)
Section Discr_Func.
  Context {C : Category} {A : Type} (Omap : A → C).

  Local Hint Extern 1 => cbn.
  
  Program Instance Discr_Func : Functor (Discr_Cat A) C :=
    {
      FO := Omap;
      
      FA := fun (a b : A) (h : a = b) =>
            match h in _ = y return (Hom (Omap y) (Omap y)) with
              | eq_refl => id
            end
    }.    
  
End Discr_Func.

Arguments Discr_Func {_ _} _, _ {_} _.

Local Hint Extern 1 => let z := fresh in extensionality z.
Local Hint Extern 1 => match goal with [z : Arrow (Discr_Cat _) |- _] => destruct z as [? ? []] end.

(* The fact that in discrete category object type and arrow type are isomorphic *)
Instance Discr_Hom_Iso (A : Type) : A ≡≡ Arrow (Discr_Cat A) ::> Type_Cat.
Proof.
  eapply (Build_Isomorphism Type_Cat _ _ (λ a, (Build_Arrow (Discr_Cat A) _ _ (eq_refl a))) (λ a : (Arrow (Discr_Cat _)), Orig a)); auto.
Qed.

Section Discretize.
  Context {C D : Category} {F G : Functor C D} (N : NatTrans F G).

  Local Hint Extern 1 => cbn.
  
  Program Instance Discretize : NatTrans (Discr_Func (F _o)) (Discr_Func (G _o)) :=
    {
      Trans := Trans N
    }.
    
End Discretize.