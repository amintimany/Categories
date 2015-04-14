Require Import Category.Main.
Require Import Basic_Cons.Equalizer.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := idtac.

Section Equalizer.
  Context {A B : Type} (f g : A → B).

  Program Instance Type_Cat_Eq : Equalizer f g :=
    {
      equalizer := {x : A | f x = g x};
      equalizer_morph := @proj1_sig _ _
    }.

  Next Obligation.
  Proof.
    extensionality x; destruct x as [x Px]; trivial.
  Qed.  

  Next Obligation.
  Proof.  
    intros T eqm H x.
    exists (eqm x); apply (fun w => equal_f w x) in H; trivial.
  Defined.

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
    destruct (proof_irrelevance _ e e').
    trivial.
  Qed.

End Equalizer.
  
Program Instance Type_Cat_Has_Equalizers : Has_Equalizers Type_Cat := fun _ _ => Type_Cat_Eq.

Require Import Coq.Relations.Relations Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ClassicalChoice Coq.Logic.ChoiceFacts.
Require Coq.Logic.ClassicalFacts.
                                         
Section CoEqualizer.
  Context {A B : Type} (f g : A → B).

  Local Obligation Tactic := idtac.
  
  Definition CoEq_rel_base : relation B := fun x y => exists z, f z = x ∧ g z = y.

  Definition CoEq_rel : relation B := clos_refl_sym_trans _ CoEq_rel_base.

  Definition CoEq_rel_refl := equiv_refl _ _ (clos_rst_is_equiv _ CoEq_rel_base).
  Definition CoEq_rel_sym := equiv_sym _ _ (clos_rst_is_equiv _ CoEq_rel_base).
  Definition CoEq_rel_trans := equiv_trans _ _ (clos_rst_is_equiv _ CoEq_rel_base).

  Definition CoEq_Type := {P : B → Prop | exists z : B, P z ∧ (∀ (y : B), (P y ↔ CoEq_rel z y))}.

  Local Axiom ConstructiveIndefiniteDescription_B : ConstructiveIndefiniteDescription_on B.
  
  Definition CoEq_Choice (ct : CoEq_Type) : {x : B | (proj1_sig ct) x}.
  Proof.
    apply ConstructiveIndefiniteDescription_B.
    destruct ct as [P [z [H1 H2]]].
    exists z; trivial.
  Defined.

  Local Axiom PropExt : ClassicalFacts.prop_extensionality.

  Theorem CoEq_rel_Ext : ∀ (x : A) (y : B), CoEq_rel (f x) y = CoEq_rel (g x) y.
  Proof.
    intros x y.
    assert (Hx : CoEq_rel (f x) (g x)).
    {
      constructor 1.
      exists x; split; trivial.
    }
    apply PropExt; split; intros H.
    {
      apply CoEq_rel_sym in Hx.
      apply (CoEq_rel_trans _ _ _ Hx H).
    }
    {
      apply (CoEq_rel_trans _ _ _ Hx H).
    }
  Qed.    
    
  Program Instance Type_Cat_CoEq  : CoEqualizer f g :=
    {|
      equalizer := CoEq_Type
    |}.

  Next Obligation.
  Proof.  
    cbn in *.
    intros x.
    exists (fun y => CoEq_rel x y).
    exists x; split.
    apply CoEq_rel_refl.
    intros z; split; intros; trivial.
  Defined.
 
  Next Obligation.
  Proof.
    extensionality x.
    apply sig_proof_irrelevance.
    extensionality y.
    apply CoEq_rel_Ext.
  Qed.    

  Next Obligation.
  Proof.  
    intros T F H x.
    exact (F (proj1_sig (CoEq_Choice x))).
  Defined.

  Next Obligation.
  Proof.
    intros T eqm H.
    unfold Type_Cat_CoEq_obligation_1, Type_Cat_CoEq_obligation_3.
    extensionality x.
    cbn in *.
    match goal with
      [|- eqm (proj1_sig ?A) = _] =>
      destruct A as [z Hz]
    end.
    cbn in *.
    induction Hz as [? ? [w [[] []]]| | |]; auto.
    {
      eapply equal_f in H; eauto.
    }
    {
      etransitivity; eauto.
    }
  Qed.

  Next Obligation.
  Proof.
    intros T eqm H1 u u' H2 H3.
    destruct H3.
    extensionality x.
    destruct x as [P [z [Hz1 Hz2]]].
    unfold Type_Cat_CoEq_obligation_1 in H2; cbn in *.
    apply equal_f with (x := z) in H2.
    match goal with
      [|- ?A = ?B] =>
      match type of H2 with
        ?C = ?D => cutrewrite (A = C); [cutrewrite (B = D)|]; trivial
      end
    end.
    {    
      erewrite sig_proof_irrelevance.
      reflexivity.
      extensionality y; apply PropExt; trivial.
    }
    {
      erewrite sig_proof_irrelevance.
      reflexivity.
      extensionality y; apply PropExt; trivial.
    }
  Qed.

End CoEqualizer.

Program Instance Type_Cat_Has_CoEqualizers : Has_CoEqualizers Type_Cat := fun _ _ => Type_Cat_CoEq.
