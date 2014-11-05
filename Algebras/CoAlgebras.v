Require Import Category.Main.
Require Import Functor.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Class CoAlgebra `{C : Category Obj Hom} (T : Functor C C) : Type :=
{
  CoAlg_Carrier : Obj;
  Destructors : Hom CoAlg_Carrier (T _o CoAlg_Carrier)
}.

Class CoAlgebra_Hom `{C : Category Obj Hom} {T : Functor C C} (calg calg' : CoAlgebra T) : Type :=
{
  coalg_map : Hom (@CoAlg_Carrier _ _ _ _ calg) (@CoAlg_Carrier _ _ _ _ calg');

  coalg_map_com : (@Destructors _ _ _ _ calg') ∘ coalg_map =  (T _a _ _ coalg_map) ∘ (@Destructors _ _ _ _ calg)
}.

Lemma CoAlgebra_Hom_eq_simplify `{C : Category Obj Hom} {T : Functor C C} (calg calg' : CoAlgebra T) (cah cah' : CoAlgebra_Hom calg calg') : (@coalg_map _ _ _ _ _ _ cah) = (@coalg_map _ _ _ _ _ _ cah') -> cah = cah'.
Proof.
  intros H1.
  destruct cah as [cahm cahc]; destruct cah' as [cahm' cahc']; simpl in *.
  destruct H1.
  destruct (proof_irrelevance _ cahc cahc').
  trivial.
Qed.

Program Instance CoAlgebra_Hom_compose `{C : Category Obj Hom} {T : Functor C C} {calg calg' calg'' : CoAlgebra T} (h : CoAlgebra_Hom calg calg') (h' : CoAlgebra_Hom calg' calg'') : CoAlgebra_Hom calg calg'' :=
{
  coalg_map := (@coalg_map _ _ _ _ _ _ h') ∘ (@coalg_map _ _ _ _ _ _ h) 
}.

Next Obligation. (* alg_map_com *)
Proof.
  destruct h as [coalm coalmcm]; destruct h' as [coalm' coalmcm'].
  unfold coalg_map.
  assert (H := @F_compose _ _ _ _ _ _ T _ _ _ coalm coalm').
  rewrite H.
  match goal with [ |- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
  rewrite coalmcm'.
  match goal with [ |- (?A ∘ ?B) ∘ ?C = ?D] => reveal_comp B C end.
  rewrite coalmcm.
  rewrite assoc; trivial.
Qed.

(* Algebra_Hom_compose defined! *)


Theorem CoAlgebra_Hom_compose_assoc `{C : Category Obj Hom} {T : Functor C C} {calg calg' calg'' calg''' : CoAlgebra T} (f : CoAlgebra_Hom calg calg') (g : CoAlgebra_Hom calg' calg'') (h : CoAlgebra_Hom calg'' calg''') :
  (CoAlgebra_Hom_compose f (CoAlgebra_Hom_compose g h)) = (CoAlgebra_Hom_compose (CoAlgebra_Hom_compose f g) h).
Proof.
  apply CoAlgebra_Hom_eq_simplify; simpl; rewrite assoc; reflexivity.
Qed.

Program Instance CoAlgebra_Hom_id `{C : Category Obj Hom} {T : Functor C C} (calg : CoAlgebra T) : CoAlgebra_Hom calg calg :=
{
  coalg_map := (@id _ _ _ (@CoAlg_Carrier _ _ _ _ calg))
}.

(* Algebra_Hom_id Defined *)

Theorem CoAlgebra_Hom_id_unit_left `{C : Category Obj Hom} {T : Functor C C} {calg calg' : CoAlgebra T} (f : CoAlgebra_Hom calg calg') :
  (CoAlgebra_Hom_compose f (CoAlgebra_Hom_id calg')) = f.
Proof.
  apply CoAlgebra_Hom_eq_simplify; simpl; simpl_ids; reflexivity.
Qed.

Theorem CoAlgebra_Hom_id_unit_right `{C : Category Obj Hom} {T : Functor C C} {calg calg' : CoAlgebra T} (f : CoAlgebra_Hom calg calg') :
  (CoAlgebra_Hom_compose (CoAlgebra_Hom_id calg) f) = f.
Proof.
  apply CoAlgebra_Hom_eq_simplify; simpl; simpl_ids; reflexivity.
Qed.

Instance CoAlgebra_Cat `{C : Category Obj Hom} (T : Functor C C) : Category (CoAlgebra T) (λ calg calg', CoAlgebra_Hom calg calg') :=
{
  compose := @CoAlgebra_Hom_compose _ _ _ T;

  assoc := @CoAlgebra_Hom_compose_assoc _ _ _ T;

  assoc_sym := fun _ _ _ _ _ _ _ => eq_sym (@CoAlgebra_Hom_compose_assoc _ _ _ T _ _ _ _ _ _ _);

  id := @CoAlgebra_Hom_id _ _ _ T;

  id_unit_left := @CoAlgebra_Hom_id_unit_left _ _ _ T;

  id_unit_right := @CoAlgebra_Hom_id_unit_right _ _ _ T
               
}.


