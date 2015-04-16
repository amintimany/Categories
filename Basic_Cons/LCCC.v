Require Import Category.Main.
Require Import Basic_Cons.CCC Basic_Cons.PullBack.
Require Import Ext_Cons.Comma.
Require Import Ext_Cons.Arrow.
Require Import Archetypal.Discr.
Require Import Functor.Const_Func Functor.Functor_Ops.

Section Slice_Terminal.
  Context (C : Category) (c : C).

  Local Notation CA z := (Build_Comma_Obj (Functor_id C) (Const_Func 1 c) _ tt z) (only parsing).
  
  Program Instance Slice_Terminal : Terminal (Slice C c) :=
    {
      terminal := CA id;
      t_morph := fun d => {|CMH_left := (CMO_hom d); CMH_right := match (CMO_trg d) as u return Hom 1 u tt with tt => id end|}
    }.

  Next Obligation.
  Proof.
    apply Comma_Hom_eq_simplify.
    set (W := eq_trans (eq_sym (CMH_com f)) (CMH_com g)); cbn in W; simpl_ids in W; trivial.
    match goal with [|- ?A = ?B] => destruct A; destruct B; trivial end.
  Qed.    

End Slice_Terminal.
  
Section PullBack_Slice_Prod.
  Context {C : Category} {c : C} {f g : Slice C c} (PB : PullBack (CMO_hom f) (CMO_hom g)).

  Local Notation CA z := (Build_Comma_Obj (Functor_id C) (Const_Func 1 c) _ tt z) (only parsing).
  
  Program Instance PullBack_Slice_Prod : @Product (Slice C c) f g :=
    {
      product := CA ((CMO_hom f) ∘ (pullback_morph_1 PB));
      Pi_1 := {|CMH_left := pullback_morph_1 PB; CMH_right := match (CMO_trg f) as u return Hom 1 u tt with tt => id end|};
      Pi_2 := {|CMH_left := pullback_morph_2 PB; CMH_right := match (CMO_trg g) as u return Hom 1 u tt with tt => id end|};
      Prod_morph_ex :=
        fun _ r1 r2 =>
          Build_Comma_Hom _ _ _ (CA ((CMO_hom f) ∘ pullback_morph_1 PB)) (pullback_morph_ex PB _ (CMH_left r1) (CMH_left r2) (eq_trans (eq_sym (CMH_com r1)) (CMH_com r2))) tt (eq_sym (eq_trans (assoc  _ _ _) (eq_trans (f_equal (fun x => compose x (CMO_hom f)) (pullback_morph_ex_com_1 PB _ (CMH_left r1) (CMH_left r2) (eq_trans (eq_sym (CMH_com r1)) (CMH_com r2)))) (eq_sym (CMH_com r1)))))
    }.

  Local Obligation Tactic := idtac.  
  
  Next Obligation.
  Proof.
    cbn; simpl_ids; apply pullback_morph_com.
  Qed.    

  Next Obligation.
  Proof.
    intros p r1 r2.
    apply Comma_Hom_eq_simplify.
    apply pullback_morph_ex_com_1.
    match goal with [|- _ = ?A] => destruct A; trivial end.
  Qed.    

  Next Obligation.
  Proof.
    intros p r1 r2.
    apply Comma_Hom_eq_simplify.
    apply pullback_morph_ex_com_2.
    match goal with [|- _ = ?A] => destruct A; trivial end.
  Qed.

  Next Obligation.
  Proof.
    intros p r1 r2 h h' H1 H2 H3 H4.
    destruct H3; destruct H4.
    set (H1' := f_equal CMH_left H1); clearbody H1'; clear H1.
    set (H2' := f_equal CMH_left H2); clearbody H2'; clear H2.
    cbn in H1', H2'.
    apply Comma_Hom_eq_simplify; cbn in *.
    {
      apply (pullback_morph_ex_unique PB _ (pullback_morph_1 PB ∘ CMH_left h) (pullback_morph_2 PB ∘ CMH_left h)); auto.
      repeat rewrite assoc_sym.
      apply (f_equal (fun x => compose _ x)).
      apply (pullback_morph_com PB).
    }    
    {
      match goal with [|- ?A = ?B] => destruct A; destruct B; trivial end.
    }    
  Qed.

End PullBack_Slice_Prod.

Section Slice_Prod_PullBack.
  Context {C : Category} {c : C} {f g : Slice C c}.

  Local Notation CA z := (Build_Comma_Obj (Functor_id C) (Const_Func 1 c) _ tt z) (only parsing).

  Context (PR : Product f g).
  
  Program Instance Slice_Prod_PullBack : PullBack (CMO_hom f) (CMO_hom g) :=
    {
      pullback := (CMO_src (@product _ _ _ PR));
      pullback_morph_1 := CMH_left (Pi_1 PR);
      pullback_morph_2 := CMH_left (Pi_2 PR);
      pullback_morph_ex := fun p r1 r2 H => CMH_left (Prod_morph_ex PR (CA ((CMO_hom f) ∘ r1)) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) f r1 tt (id_unit_left _ _ _)) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) g r2 tt (eq_trans (id_unit_left _ _ _) H)))
    }.

  Local Obligation Tactic := idtac.  
  
  Next Obligation.
  Proof.
    exact (eq_trans (eq_sym (CMH_com (Pi_1 PR))) (CMH_com (Pi_2 PR))).
  Qed.

  Next Obligation.
  Proof.
    intros p r1 r2 H.
    cbn in *.
    exact (f_equal CMH_left (Prod_morph_com_1 PR (CA ((CMO_hom f) ∘ r1)) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) f r1 tt _) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) g r2 tt _))).
  Qed.
  
  Next Obligation.
  Proof.
    intros p r1 r2 H.
    cbn in *.
    exact (f_equal CMH_left (Prod_morph_com_2 PR (CA ((CMO_hom f) ∘ r1)) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) f r1 tt _) (Build_Comma_Hom _ _ (CA ((CMO_hom f) ∘ r1)) g r2 tt _))).
  Qed.

  Next Obligation.
  Proof.
    intros p r1 r2 H h1 h2 H1 H2 H3 H4.
    destruct H3; destruct H4.
    evar (V1T : Type); evar (V1 : V1T).
    change h1 with (CMH_left (Build_Comma_Hom _ _ (CA (CMO_hom f ∘ CMH_left (Pi_1 PR) ∘ h2)) (@product _ _ _ PR) h1 tt V1)).
    evar (V2T : Type); evar (V2 : V2T).
    change h2 with (CMH_left (Build_Comma_Hom _ _ (CA (CMO_hom f ∘ CMH_left (Pi_1 PR) ∘ h2)) (@product _ _ _ PR) h2 tt V2)).
    apply f_equal.
    eapply (Prod_morph_unique PR (CA (CMO_hom f ∘ CMH_left (Pi_1 PR) ∘ h2))); eauto; apply Comma_Hom_eq_simplify; auto.
    Unshelve.
    {
      unfold V1T; clear V1T; cbn.
      set (W := f_equal (compose h1) (CMH_com (Pi_1 PR))).
      cbn in W.
      repeat rewrite assoc in W.
      set (N := (eq_trans (id_unit_left _ _ _) (f_equal (fun x => compose x (CMO_hom f)) (eq_sym H1)))).
      cbn in N.
      rewrite N.
      symmetry.
      auto.
    }
    {
      cbn in *.
      unfold V2T; clear V1 V1T V2T; cbn.
      set (W := f_equal (compose h2) (CMH_com (Pi_1 PR))).
      cbn in W.
      repeat rewrite assoc in W.
      set (N := (eq_trans (id_unit_left _ _ _) (f_equal (fun x => compose x (CMO_hom f)) (eq_sym H1)))).
      cbn in N.
      rewrite N.
      symmetry.
      rewrite H1.
      auto.
    }
  Qed.

End Slice_Prod_PullBack.

Section Has_PullBack_Slice_Has_Prod.
  Context {C : Category} (HPB : Has_PullBacks C) (c : C).

  Instance Has_PullBack_Slice_Has_Prod : Has_Products (Slice C c) := fun f g => PullBack_Slice_Prod (HPB _ _ _ (CMO_hom f) (CMO_hom g)).

End Has_PullBack_Slice_Has_Prod.

Section Slice_Has_Prod_Has_PullBack.
  Context {C : Category} (HPR : ∀ c : C, Has_Products (Slice C c)).

  Instance Slice_Has_Prod_Has_PullBack : Has_PullBacks C := fun a b c f g => Slice_Prod_PullBack (HPR _ (Build_Comma_Obj (Functor_id C) (Const_Func 1 c) _ tt f) (Build_Comma_Obj (Functor_id C) (Const_Func 1 c) _ tt g)).
  
End Slice_Has_Prod_Has_PullBack.
    
(* Locally Cartesian Closed Category : one in which all slices are cartesian closed *)
Definition LCCC (C : Category) : Type := ∀ (c : C), CCC (Slice C c).


