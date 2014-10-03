Require Import Category.Core.
Require Import Functor.Core.

Class Algebra `{C : Category Obj} (T : Functor C C) : Type :=
{
  Alg_Carrier : Obj;
  Constructors : Hom (T _o Alg_Carrier) Alg_Carrier
}.

Class Algebra_Hom `{C : Category Obj Hom} {T : Functor C C} (alg alg' : Algebra T) : Type :=
{
  alg_map : Hom (@Alg_Carrier _ _ _ _ alg) (@Alg_Carrier _ _ _ _ alg');

  alg_map_com : (@Constructors _ _ _ _ alg') ∘ (T _a _ _ alg_map) = alg_map ∘ (@Constructors _ _ _ _ alg)
}.

(* Algebra_Hom_eq_Setoid Defined! *)


Program Instance Algebra_Hom_compose `{C : Category Obj Hom} {T : Functor C C} {alg alg' alg'' : Algebra T} (h : Algebra_Hom alg alg') (h' : Algebra_Hom alg' alg'') : Algebra_Hom alg alg'' :=
{
  alg_map := (@alg_map _ _ _ _ _ _ h') ∘ (@alg_map _ _ _ _ _ _ h) 
}.

Next Obligation. (* alg_map_com *)
Proof.
  destruct h as [alm almcm]; destruct h' as [alm' almcm'].
  unfold alg_map.
  assert (H := @F_compose _ _ _ _ _ _ T _ _ _ alm alm').
  rewrite H.
  match goal with [ |- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
  rewrite almcm'.
  match goal with [ |- (?A ∘ ?B) ∘ ?C = ?D] => reveal_comp B C end.
  rewrite almcm.
  rewrite assoc; trivial.
Qed.

(* Algebra_Hom_compose defined! *)

Lemma Algebra_Hom_eq_simplify `{C : Category Obj Hom} {T : Functor C C} (alg alg' : Algebra T) (ah ah' : Algebra_Hom alg alg') : (@alg_map _ _ _ _ _ _ ah) = (@alg_map _ _ _ _ _ _ ah') -> ah = ah'.
Proof.
  intros H1.
  destruct ah as [ahm ahc]; destruct ah' as [ahm' ahc']; simpl in *.
  destruct H1.
  destruct (proof_irrelevance _ ahc ahc').
  trivial.
Qed.


Theorem Algebra_Hom_compose_assoc `{C : Category Obj} {T : Functor C C} {alg alg' alg'' alg''' : Algebra T} (f : Algebra_Hom alg alg') (g : Algebra_Hom alg' alg'') (h : Algebra_Hom alg'' alg''') :
  (Algebra_Hom_compose f (Algebra_Hom_compose g h)) = (Algebra_Hom_compose (Algebra_Hom_compose f g) h).
Proof.
  apply Algebra_Hom_eq_simplify; simpl; rewrite assoc; trivial.
Qed.

Program Instance Algebra_Hom_id `{C : Category Obj Hom} {T : Functor C C} (alg : Algebra T) : Algebra_Hom alg alg :=
{
  alg_map := (@id _ _ _ (@Alg_Carrier _ _ _ _ alg))
}.

(* Algebra_Hom_id Defined *)

Theorem Algebra_Hom_id_unit_left `{C : Category Obj Hom} {T : Functor C C} {alg alg' : Algebra T} (f : Algebra_Hom alg alg') :
  (Algebra_Hom_compose f (Algebra_Hom_id alg')) = f.
Proof.
  apply Algebra_Hom_eq_simplify; simpl; simpl_ids; reflexivity.
Qed.

Theorem Algebra_Hom_id_unit_right `{C : Category Obj Hom} {T : Functor C C} {alg alg' : Algebra T} (f : Algebra_Hom alg alg') :
  (Algebra_Hom_compose (Algebra_Hom_id alg) f) = f.
Proof.
  apply Algebra_Hom_eq_simplify; simpl; simpl_ids; reflexivity.
Qed.

Instance Algebra_Cat `{C : Category Obj} (T : Functor C C) : Category (Algebra T) (λ alg alg', Algebra_Hom alg alg') :=
{
  compose := @Algebra_Hom_compose _ _ _ T;

  assoc := @Algebra_Hom_compose_assoc _ _ _ T;
  
  assoc_sym := fun _ _ _ _ _ _ _ => eq_sym (@Algebra_Hom_compose_assoc _ _ _ T _ _ _ _ _ _ _);

  id := @Algebra_Hom_id _ _ _ T;

  id_unit_left := @Algebra_Hom_id_unit_left _ _ _ T;

  id_unit_right := @Algebra_Hom_id_unit_right _ _ _ T
               
}.


