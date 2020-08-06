From Coq.Relations Require Import Relations Relation_Definitions.
From Categories.Essentials Require Import Notations Types Facts_Tactics Quotient.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.Equalizer.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := idtac.

(** Just like in category of sets, in category of types, the equalizer is the
    type that reperesents the subset of the cartesian profuct of the domain of
    the two functions that is mapped to equal values by both functions. *)
Section Equalizer.
  Context {A B : Type} (f g : A → B).

  Program Definition Type_Cat_Eq : Equalizer Type_Cat f g :=
    {|
      equalizer := {x : A | f x = g x};
      equalizer_morph := @proj1_sig _ _;
      equalizer_morph_ex :=
        fun T eqm H x =>
          exist _ (eqm x) _
    |}.

  Next Obligation.
  Proof.
    extensionality x; destruct x as [x Px]; trivial.
  Qed.

  Next Obligation.
  Proof.
    intros T eqm H x.
    apply (fun w => equal_f w x) in H; trivial.
  Qed.

  Next Obligation.
  Proof.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros T eqm H1 u u' H2 H3.
    extensionality x.
    apply (fun w => equal_f w x) in H2; cbn in H2.
    apply (fun w => equal_f w x) in H3; cbn in H3.
    destruct (u x) as [ux e]; destruct (u' x) as [ux' e']; cbn in *.
    destruct H2; destruct H3.
    PIR.
    trivial.
  Qed.

End Equalizer.

(** Similar to the category set, in category of types, the coequalizer of two
    functions f,g : A -> B is quotient of B with respect to the equivalence
relation ~. Here, ~ is the equivalence closure of the relation for which we have

x ~ y if and only if ∃z. (f(z) = x) ∧ (g(z) = y)

*)


Program Instance Type_Cat_Has_Equalizers : Has_Equalizers Type_Cat :=
  fun _ _ => Type_Cat_Eq.

Section CoEqualizer.
  Context {A B : Type} (f g : A → B).

  Local Obligation Tactic := idtac.

  Definition CoEq_rel_base : relation B := fun x y => exists z, f z = x ∧ g z = y.

  Program Definition CoEq_rel : EquiRel B :=
    {| EQR_rel := clos_refl_sym_trans _ CoEq_rel_base |}.
  Next Obligation.
  Proof.
    split.
    exact (equiv_refl _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
    exact (equiv_sym _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
    exact (equiv_trans _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
  Qed.

  Program Definition Type_Cat_CoEq  : CoEqualizer Type_Cat f g :=
    {|
      equalizer := quotient CoEq_rel;
      equalizer_morph := λ x, class_of CoEq_rel x;
      equalizer_morph_ex e' F H x := F (representative x)
    |}.

  Next Obligation.
  Proof.
    extensionality x; simpl.
    apply class_of_inj.
    constructor; exists x; eauto.
  Qed.

  Next Obligation.
  Proof.
    intros T eqm Hfg; simpl.
    extensionality x.
    induction (representative_of_class_of CoEq_rel x)
      as [? ? [w [[] []]]| | |]; auto; [].
    apply (equal_f Hfg).
  Qed.

  Next Obligation.
  Proof.
    intros T eqm Hfg u u' Hu <-; simpl in *.
    extensionality x.
    rewrite <- (class_of_representative CoEq_rel x).
    apply (equal_f Hu).
  Qed.

End CoEqualizer.

Program Instance Type_Cat_Has_CoEqualizers : Has_CoEqualizers Type_Cat :=
  fun _ _ => Type_Cat_CoEq.
