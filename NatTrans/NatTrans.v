From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.
From Categories Require Import Cat.Cat.

(**
For categories C and C' and functors F : C -> C' and F' : C -> C', a natural
transformation N : F -> F' is a family of arrows 'Trans N' in the co-domain
category (here C') indexed by objects of the domain category (here C),
Trans N c : F _o c -> F' _o c.

In addition, for all arrows h : c → c' the following diagram must
commute (Trans_com):

#
<pre>
             F _a h
F _o c ————————————————––> F _o c'
 |                          |
 |                          |
 |                          |
 | Trans N c                | Trans N c'
 |                          |
 |                          |
 ∨                          ∨
F' _o c ————————————————–> F' _o c'
            F' _a h
</pre>
#
Trans_com_sym is the symmetric form of Trans_com.
*)
Record natural {C C' : category} (F F' : functor C C') :=
  {
    trans (c : C) : hom (F ₒ c) (F' ₒ c);
    naturality {c c' : C} (h : hom c c') :
      ((trans c') ∘ F ₐ h = F' ₐ h ∘ (trans c))%morphism;
    naturality_sym {c c' : C} (h : hom c c') :
      (F' ₐ h ∘ (trans c) = (trans c') ∘ F ₐ h)%morphism
  }.

Arguments trans {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.
Arguments naturality_sym {_ _ _ _} _ {_ _} _.

Coercion trans : natural >-> Funclass.

(** Two natural transformations are equal if their arrow families are.
    That is, commutative diagrams are assumed to be equal by
    proof irrelevance. *)
Lemma natural_eq_simplify {C C' : category} {F F' : functor C C'}
      (N N' : natural F F') : (trans N) = (trans N') -> N = N'.
Proof. destruct N; destruct N'; basic_simpl; ElimEq; PIR; trivial. Qed.

Bind Scope nattrans_scope with natural.

Local Open Scope nattrans_scope.

(** Natural transformations are composable. The arrow family of the result is
      just the composition of corresponding components in each natural
      transformation. Graphically:
#
<pre>
         F                            F
   C ———————————————–> D        C ———————————————–> D 
           ||                           ||
           ||N                          ||
           ||                           ||
           \/                           ||
   C ———————————————–> D                || N' ∘ N
         G                              ||
           ||                           ||
           ||N'                         ||
           ||                           ||
           \/                           \/
   C ———————————————–> D        C ———————————————–> D 
         H                            H
</pre>
#

This kind of composition is sometimes also called vertical composition of
natural transformations.
*)
Program Definition natural_compose {C C' : category} {F F' F'' : functor C C'}
        (tr : natural F F') (tr' : natural F' F'') : natural F F'' :=
  {|
    trans := fun c => ((trans tr' c) ∘ (trans tr c))%morphism
  |}.
Next Obligation. (* naturality *)
Proof. intros ??????????; rewrite assoc naturality -assoc naturality; auto. Qed.
Next Obligation. (* naturality_sym *)
Proof. intros ??????????; rewrite /= assoc naturality -assoc -naturality; auto. Qed.
Fail Next Obligation.

Notation "N ∘ N'" := (natural_compose N' N) : nattrans_scope.

(** The composition of natural transformations is associative. *)
Theorem natural_compose_assoc {C C' : category} {F G H I : functor C C'} (N : natural F G)
  (N' : natural G H) (N'' : natural H I) : ((N'' ∘ N') ∘ N = N'' ∘ (N' ∘ N))%nattrans.
Proof. apply natural_eq_simplify; cbn; auto. Qed.

(** The identity natural transformation. The arrow family are just
    all identity arrows: *)
Program Definition natural_id {C C' : category} (F : functor C C') : natural F F :=
  {|
    trans c := id (F ₒ c)
  |}.
Solve All Obligations with repeat intros ?; simpl; auto.  
Fail Next Obligation.

Theorem natural_id_unit_left {C C' : category} {F G : functor C C'} (N : natural F G) : (natural_id G) ∘ N = N.
Proof. apply natural_eq_simplify; cbn; auto. Qed.

Theorem natural_id_unit_right {C C' : category} {F G : functor C C'} (N : natural F G) : N ∘ (natural_id F) = N.
Proof. apply natural_eq_simplify; cbn; auto. Qed.

Hint Resolve natural_eq_simplify : core.
