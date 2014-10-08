Require Import Category.Core.
Require Import Functor.Core.
Require Import Basic_Cons.Core.
Require Import Coq_Cats.Type_Cat.
Require Import Algebras.Core.

Program Instance S_nat_func : Functor Type_Cat Type_Cat :=
{
  FO := λ a, (_T_ Type_Cat) ⊕ a ;
  FA := λ a b f, 〚 @id _ _ _ (_T_ Type_Cat), f 〛
}.

Next Obligation. (* mapping of identities *)
Proof.
  extensionality x.
  destruct x as [a|x]; trivial.
Qed.

Next Obligation. (* functor commuting with compose *)
Proof.
  extensionality x.
  destruct x as [m|x]; trivial.
Qed.

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

Program Instance nat_alg_init : Initial S_nat_alg_cat nat_alg :=
{
  i_morph := nat_alg_morph
}.

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
Program Instance CoNat_coalg_morph coalg' : CoAlgebra_Hom coalg' CoNat_coalg.

Next Obligation. (* coalg_map *)
Proof.
  destruct coalg' as [coalgc' coalgdest'].
  red in X.
  exact(
      (cofix m (x : coalgc') :=
         match (coalgdest' x) with
           | inl _ => CoO
           | inr x' => CoS (m x')
         end) X
    ).
Defined.

Next Obligation. (* coalg_map_com *)
Proof.
  destruct coalg' as [coalgc' coalgdest'].
  extensionality x.
  red in x.
  cbv.
  destruct (coalgdest' x) as [[]|x']; trivial.
Qed.

(* CoNat_coalg_morph defined *)

Program Instance CoNat_alg_term : Terminal S_nat_coalg_cat CoNat_coalg :=
{
  t_morph := CoNat_coalg_morph
}.

Next Obligation. (* t_morph_unique *)
Proof.
  destruct d as [coalgc algdest].
  destruct f as [f_morph f_com].
  destruct g as [g_morph g_com].
  cbv.
  apply CoAlgebra_Hom_eq_simplify.
  extensionality x; simpl.
   apply CoNat_eq_eq; revert x.
  cofix H.
  intros x.
  assert(H1 := equal_f f_com x); cbv in H1.
  assert(H2 := equal_f g_com x); cbv in H2.
  destruct (algdest x) as [[]|x'].
  destruct (f_morph x); destruct (g_morph x); try discriminate.
  constructor.
  destruct (f_morph x); destruct (g_morph x); try discriminate.
  inversion H1; inversion H2; subst.
  constructor.
  apply H.
Qed.

(* CoNat_coalg_term Proved! :-) *)









