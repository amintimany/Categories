Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Coq_Cats.Type_Cat.Facts.
Require Import Algebras.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Cat.Facts.


Program Instance term_id : Functor Type_Cat (Prod_Cat Type_Cat Type_Cat) :=
{
  FO := fun a => (@CCC_term Type_Cat _, a);
  FA := fun a b f => (@id _ (@CCC_term Type_Cat _), f)
}.

Instance S_nat_func : Functor Type_Cat Type_Cat := Functor_compose term_id (@Sum_Func Type_Cat _).

(* S_nat_func defined *)

Definition S_nat_alg_cat := Algebra_Cat S_nat_func.

Instance nat_alg : Algebra S_nat_func :=
{
  Alg_Carrier := nat;
  Constructors :=
    fun x =>
      match x with
        | inl a => 0
        | inr n => S n
      end
}.

(* morphism from nat_alg to another alg *)
Program Instance nat_alg_morph alg' : Algebra_Hom nat_alg alg'.

Next Obligation. (* alg_map *)
Proof.
  destruct alg' as [algc' algcons'].
  exact(
      (fix m (n : nat) :=
        match n with
          | O => algcons' (inl tt)
          | S n' => algcons' (inr (m n'))
        end) H
    ).
Defined.

Next Obligation. (* alg_map_com *)
Proof.
  destruct alg' as [algc' algcons'].
  extensionality x.
  destruct x as [[]|x]; simpl; trivial.
Qed.

(* nat_alg_morph defined *)

Program Instance nat_alg_init : Initial S_nat_alg_cat :=
{|
  terminal := nat_alg;
  t_morph := nat_alg_morph
|}.

Next Obligation. (* i_morph_unique *)
Proof.
  destruct d as [algc algcons].
  destruct f as [f_morph f_com].
  destruct g as [g_morph g_com].
  cbv.
  apply Algebra_Hom_eq_simplify.
  extensionality x.
  simpl.
  induction x.
  {
    assert(H1 := equal_f f_com (inl tt)); cbv in H1; rewrite <- H1.
    assert(H2 := equal_f g_com (inl tt)); cbv in H2; rewrite <- H2.
    trivial.
  }
  {
    assert(H1 := equal_f f_com (inr x)); cbv in H1; rewrite <- H1.
    assert(H2 := equal_f g_com (inr x)); cbv in H2; rewrite <- H2.
    rewrite IHx.
    trivial.
  }
Qed.

(* nat_alg_init Proved! :-) *)










CoInductive CoNat : Type :=
  | CoO : CoNat
  | CoS : CoNat -> CoNat
.

CoInductive CoNat_eq : CoNat -> CoNat -> Prop :=
  | CNOeq : CoNat_eq CoO CoO
  | CNSeq : forall (n n' : CoNat), CoNat_eq n n' -> CoNat_eq (CoS n) (CoS n')
.

Axiom CoNat_eq_eq : forall (n n' : CoNat), CoNat_eq n n' -> n = n'.



Definition S_nat_coalg_cat := CoAlgebra_Cat S_nat_func.

Instance CoNat_coalg : CoAlgebra S_nat_func :=
{
  CoAlg_Carrier := CoNat;
  Destructors :=
    fun x =>
      match x with
        | CoO => inl tt
        | CoS n => inr n
      end
}.

(* morphism from another alg to CoNat_coalg *)
Program Instance CoNat_coalg_morph coalg' : CoAlgebra_Hom coalg' CoNat_coalg :=
{
  coalg_map :=
    λ (H : @CoAlg_Carrier _ _ coalg'),
    (cofix m (x : @CoAlg_Carrier _ _ coalg') : CoNat :=
       match @Destructors _ _ coalg' x with
         | inl _ => CoO
         | inr x' => CoS (m x')
       end) H
}.

Next Obligation. (* coalg_map_com *)
Proof.
  extensionality x.
  destruct coalg' as [coalgc' coalgdest'].
  simpl.
  destruct (coalgdest' x) as [[]|x']; trivial.
Qed.

(* CoNat_coalg_morph defined *)

Program Instance CoNat_alg_term : Terminal S_nat_coalg_cat :=
{
  terminal := CoNat_coalg;
  t_morph := CoNat_coalg_morph
}.

Next Obligation. (* t_morph_unique *)
Proof.
  apply CoAlgebra_Hom_eq_simplify.
  extensionality x; simpl.
  apply CoNat_eq_eq; revert x.
  cofix H.
  intros x.
  assert(H1 := equal_f (@coalg_map_com _ _ _ _ f) x); cbv -[coalg_map Destructors] in H1.
  assert(H2 := equal_f (@coalg_map_com _ _ _ _ g) x); cbv -[coalg_map Destructors] in H2.
  destruct (@Destructors _ _ d x); destruct ((@coalg_map _ _ _ _ f) x); destruct ((@coalg_map _ _ _ _ g) x); try discriminate; try constructor.
  inversion H1; inversion H2.
  apply H.
Qed.

(* CoNat_coalg_term Proved! *)









