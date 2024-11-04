From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import Cat.Cat.
From Categories Require Import NatTrans.NatTrans.

Local Open Scope nattrans_scope.

(** The opposite of a natural transformation N : F -> F' is a nattrans
    N^op : F'^op -> F^op. It has the same arrow family as the original
    natural transformation. *)
Program Definition opposite_natural {C D : category} {F F' : functor C D} (N : natural F F') : natural (F' ᴼᴾ) (F ᴼᴾ) :=
  {|
    trans := trans N;
    naturality := fun c c' h => (naturality_sym N h);
    naturality_sym := fun c c' h => (naturality N h)
  |}.

Notation "N 'ᴼᴾ'" := (opposite_natural N) : nattrans_scope.

(** Composition of opposite natural transformations is just the same as the
    opposite natural transformation of the composition. *)

Theorem natural_compose_op {C D : category} {F F' F'' : functor C D} (N : natural F F') (N' : natural F' F'') :
  ((N' ∘ N) ᴼᴾ = N ᴼᴾ ∘ (N' ᴼᴾ))%nattrans.
Proof. apply natural_eq_simplify; trivial. Qed.

(** Opposite of natural_id is just natural_id of the opposite functor *)
Theorem natural_id_op {C D : category} (F : functor C D) : ((natural_id F) ᴼᴾ)%nattrans = natural_id (F ᴼᴾ).
Proof. apply natural_eq_simplify; trivial. Qed.

(** Horizontal composition of natural transformations:

Let C, D and E be categories, F: C -> D G : C -> D, F' : D -> E and
G' : D -> E be functors and N : F -> G and N' : F' -> G' be natural
transformations. Then, the horizontal composition of N and N',
denoted by N ∘_h N' : F' ∘ F -> G' ∘ G is defined as follows:
 *)
Program Definition natural_hor_comp {C D E : category} {F G : functor C D} {F' G' : functor D E}
  (tr : natural F G) (tr' : natural F' G') : natural (F' ∘ F) (G' ∘ G) :=
{|
  trans c := ((G' ₐ (trans tr c)) ∘ (trans tr' (F ₒ c)))%morphism
|}.
Next Obligation.
  repeat intros ?; rewrite /= assoc naturality -assoc -F_compose naturality F_compose; auto.
Qed.
Next Obligation.
  repeat intros ?; symmetry; rewrite /= assoc naturality -assoc -F_compose naturality F_compose; auto.
Qed.
Fail Next Obligation.

(**
Graphically:
#
<pre>
    C      C             C              C
    |  N   |             |              |
  F | ===> | G           |              |
    |      |             |              |
    ∨      ∨             |   N' ∘_h N   |
    D      D        F'∘F | ===========> |G'∘G
    |  N'  |             |              |
 F' | ===> | G'          |              |
    |      |             |              |
    ∨      ∨             ∨              ∨
    E      E             E              E
</pre>
#
*)

Notation "N ∘ₕ N'" := (natural_hor_comp N' N) : nattrans_scope.

(** Horizontal composition of natural_ids is just the natural_id of
    the composition of underlying functors. *)
Theorem natural_hor_comp_ids {C D E : category} (F : functor C D) (G : functor D E) :
  ((natural_id G) ∘ₕ (natural_id F))%nattrans = natural_id  (G ∘ F).
Proof. apply natural_eq_simplify; cbn; extensionality c; rewrite F_id; simpl_ids; trivial. Qed.

(** Horizontal composition of opposite of two natural transformations is just
    the opposite of the horizontal composition of those two natural
    transformations. *)

Theorem natural_hor_comp_op {C D E : category} {F G : functor C D} {F' G' : functor D E} (N : natural F G) (N' : natural F' G') :
  ((N' ∘ₕ N) ᴼᴾ = N' ᴼᴾ ∘ₕ N ᴼᴾ)%nattrans.
Proof. apply natural_eq_simplify; cbn; extensionality c; rewrite naturality; trivial. Qed.

(** Natural transformation from a functor to itself composed with id on
    the right. *)
Program Definition natural_to_compose_id {C D : category} (F : functor C D) : natural F ((functor_id D) ∘ F) :=
  {|
    trans c := id (F ₒ c)
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Natural transformation to a functor from itself composed with id on
    the right. *)
Program Definition natural_from_compose_id {C D : category} (F : functor C D) : natural ((functor_id D) ∘ F) F :=
  {|
    trans c := id (F ₒ c)
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Natural transformation from a functor to itself composed with id on
    the left. *)
Program Definition natural_to_id_compose {C D : category} (F : functor C D) : natural F (F ∘ (functor_id C)) :=
  {|
    trans c := id (F ₒ c)
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Natural transformation to a functor from itself composed with id on
    the left. *)
Program Definition natural_from_id_compose {C D : category} (F : functor C D) : natural (F ∘ (functor_id C)) F :=
  {|
    trans c := id (F ₒ c)
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Natural transformation corresponding to associativity of
    functor composition *)
Program Definition func_associator {C1 C2 C3 C4 : category} (F : functor C1 C2) (G : functor C2 C3) (H : functor C3 C4) :
  natural ((H ∘ G) ∘ F) (H ∘ (G ∘ F)) :=
  {|
    trans c := id (H ₒ (G ₒ (F ₒ c)))
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Natural transformation corresponding to the symmetric form of
    associativity of functor composition *)
Program Definition func_associator_sym {C1 C2 C3 C4 : category} (F : functor C1 C2) (G : functor C2 C3) (H : functor C3 C4) :
  natural (H ∘ (G ∘ F)) ((H ∘ G) ∘ F) :=
  {|
    trans c := id (H ₒ (G ₒ (F ₒ c)))
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.
(**
The following theorem states that the two natural transformations of
the diagram in the middle are equal.
#
<pre>
    F                       G ∘ F                      G
 C —————––>D   D —————————–—————————————————–—–—–> E   D —–————–> E
     ||           ||                           ||          ||
     ||N1         ||                           ||          ||N2
     ||           ||                           ||          ||
     \/           ||                           ||          \/
     F'           ||                           ||          G'
 C ————–—–>D      ||  (N4 ∘ N2) ∘ₕ (N3 ∘ N1)   ||      D ———–——–> E
     ||           ||                           ||          ||
     || N3        ||                           ||          ||N4
     ||           ||  (N4 ∘ₕ N3) ∘ (N2 ∘ₕ  N1)  ||          ||
     \/           ||                           ||          \/
     F''          \/                           \/          G''
 C ————–—–> D  D ——–—————————————————————————–——–> E   D————–——–> E
                            G'' ∘ F''
</pre>
#
*)
Theorem natural_comp_hor_comp {C D E : category} {F F' F'' : functor C D} {G G' G'' : functor D E}
  (N1 : natural F F') (N2 : natural G G') (N3 : natural F' F'') (N4 : natural G' G'') :
  ((N4 ∘ₕ N3) ∘ (N2 ∘ₕ N1) = (N4 ∘ N2) ∘ₕ (N3 ∘ N1))%nattrans.
Proof.
  apply natural_eq_simplify; extensionality c; cbn.
  rewrite F_compose !assoc; f_equal; rewrite -!assoc; f_equal.
  rewrite naturality; trivial.
Qed.

(** Equal functors produce a natural isomorphism. *)
Program Definition func_eq_to_natural {C D : category} {F G : functor C D} (FGeq : F = G) : natural F G :=
  {| trans c := hom_trans eq_refl (equal_f (f_equal FO FGeq) c) (id (F ₒ c)) |}.
Next Obligation.
Proof.
  intros ????????; simpl in *.
  rewrite hom_trans_comp_take_in_l right_id hom_trans_comp_take_in_r !hom_trans_refl left_id.
  apply hom_trans_r_to_l.
  rewrite hom_trans_trans eq_trans_refl_r eq_trans_refl_l !eq_sym_involutive.
  apply Functor_eq_morph.
Qed.
Next Obligation.
Proof.
  intros ????????; simpl in *.
  symmetry.
  rewrite hom_trans_comp_take_in_l right_id hom_trans_comp_take_in_r !hom_trans_refl left_id.
  apply hom_trans_r_to_l.
  rewrite hom_trans_trans eq_trans_refl_r eq_trans_refl_l !eq_sym_involutive.
  apply Functor_eq_morph.
Qed.
Fail Next Obligation.

Program Definition func_eq_to_natural_inverse {C D : category} {F G : functor C D} (FGeq : F = G) :
  func_eq_to_natural (eq_sym FGeq) ∘ func_eq_to_natural FGeq = natural_id F.
Proof.
  apply natural_eq_simplify; extensionality c; simpl.
  rewrite hom_trans_comp_take_in_l right_id !hom_trans_trans !eq_trans_refl_r eq_trans_refl_l.
  rewrite -equal_f_eq_sym -f_equal_eq_sym.
  rewrite -(F_id F) -(F_id G).
  apply (Functor_eq_morph (eq_sym FGeq)).
Qed.

(**
Given I : C ≃ D for categories C and D and F : D -> E, there is a natural
transformation from F ∘ (I ∘ I⁻¹) to F and back.
*)
Program Definition IsoCat_natural {C D : category} (I : C ≃@{Cat} D) {E : category} (F : functor D E) :
  natural (F ∘ ((iso_morphism I) ∘ (I⁻¹)%morphism)) F :=
  func_eq_to_natural (eq_trans (f_equal (fun G => F ∘ G)%functor (right_inverse I)) (Functor_id_unit_right _ _ F)).

Program Definition IsoCat_natural_back {C D : category} (I : C ≃@{Cat} D) {E : category} (F : functor D E) :
  natural F (F ∘ ((iso_morphism I) ∘ (I⁻¹)%morphism)) :=
  func_eq_to_natural (eq_sym (eq_trans (f_equal (fun G => F ∘ G)%functor (right_inverse I)) (Functor_id_unit_right _ _ F))).
