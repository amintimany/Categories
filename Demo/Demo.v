Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Basic_Cons.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Coq_Cats.Type_Cat.Facts.
Require Import Algebras.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.
Require Import Cat.Facts.


Program Definition term_id : (Type_Cat –≻ (Type_Cat × Type_Cat))%functor :=
{|
  FO := fun a => (@CCC_term Type_Cat _, a);
  FA := fun a b f => (@id _ (@CCC_term Type_Cat _), f)
|}.

Definition S_nat_func : (Type_Cat –≻ Type_Cat)%functor :=
  ((+ᶠⁿᶜ Type_Cat _) ∘ term_id)%functor.

(* S_nat_func defined *)

Definition S_nat_alg_cat := Algebra_Cat S_nat_func.

Program Definition nat_alg : Algebra S_nat_func :=
{|
  Alg_Carrier := nat;
  Constructors :=
    fun x =>
      match x with
        | inl a => 0
        | inr n => S n
      end
|}.

(* morphism from nat_alg to another alg *)
Program Definition nat_alg_morph alg' : Algebra_Hom nat_alg alg' :=
  {|
    Alg_map :=
      fun x =>
        (fix f (n : nat) :=
        match n with
        | O => (Constructors alg') (inl tt)
        | S n' => (Constructors alg') (inr (f n'))
        end) x
  |}.

Next Obligation. (* alg_map_com *)
Proof.
  extensionality x.
  destruct x as [|[]]; cbn; trivial.
  repeat apply f_equal.
  match goal with [A : unit |- _] => destruct A; trivial end.
Qed.

Program Definition nat_alg_init : (𝟘_ S_nat_alg_cat)%object :=
  {|
    terminal := nat_alg;
    t_morph := nat_alg_morph
  |}.

Next Obligation.
Proof.
  destruct d as [algc algcons].
  destruct f as [f_morph f_com].
  destruct g as [g_morph g_com].
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









CoInductive CoNat : Set :=
  | CoO : CoNat
  | CoS : CoNat -> CoNat
.

CoInductive CoNat_eq : CoNat -> CoNat -> Prop :=
  | CNOeq : CoNat_eq CoO CoO
  | CNSeq : forall (n n' : CoNat), CoNat_eq n n' -> CoNat_eq (CoS n) (CoS n')
.

Axiom CoNat_eq_eq : forall (n n' : CoNat), CoNat_eq n n' -> n = n'.

Definition S_nat_coalg_cat := @CoAlgebra_Cat Type_Cat S_nat_func.

Program Definition CoNat_coalg : @CoAlgebra Type_Cat S_nat_func :=
{|
  Alg_Carrier := CoNat;
  Constructors :=
    fun x : CoNat =>
       match x return unit + CoNat  with
       | CoO => inl tt
       | CoS x' => inr x'
       end
|}.

(* morphism from another alg to CoNat_coalg *)
Program Definition CoNat_coalg_morph coalg' : CoAlgebra_Hom CoNat_coalg coalg' :=
  {|
    Alg_map :=
      cofix f (x : Alg_Carrier coalg') : CoNat :=
        match Constructors coalg' x return CoNat with
        | inl _ => CoO
        | inr s => CoS (f s)
        end
|}.

Next Obligation. (* coalg_map_com *)
Proof.
  extensionality x; cbn.
  destruct (Constructors coalg' x) as [x'|x']; cbn; trivial.
  replace x' with tt; trivial.
  cbn in *.
  match goal with [A : unit |- _] => destruct A; trivial end.
Qed.

(* CoNat_coalg_morph defined *)

Program Definition CoNat_alg_term : (𝟘_ S_nat_coalg_cat)%object :=
{|
  terminal := CoNat_coalg;
  t_morph := CoNat_coalg_morph
|}.

Next Obligation.
Proof.
  apply Algebra_Hom_eq_simplify.
  extensionality x; simpl.
  apply CoNat_eq_eq; revert x.
  cofix H.
  intros x.
  assert(H1 := equal_f (@Alg_map_com _ _ _ _ f) x); cbn in H1.
  assert(H2 := equal_f (@Alg_map_com _ _ _ _ g) x); cbn in H2.
  destruct (Constructors d x); destruct ((Alg_map f) x); destruct ((Alg_map g) x); try discriminate; try constructor.
  inversion H1; inversion H2.
  trivial.
Qed.







