From Categories.Essentials Require Import Notations Facts_Tactics.
From Categories.Category Require Import Main.
From Categories.Functor Require Import Functor Functor_Ops.
From Categories.NatTrans Require Import Main.
From Categories.Adjunction Require Import Main.
From Categories.Monad Require Import Monad.

Section distributive_law.
  Context {C : Category} {F G : (C --> C)%functor}
          (Fmon : Monad F) (Gmon : Monad G)
          (ι : (F ∘ G --> G ∘ F)%nattrans).

  Record distributive_law := {
    distr_law_unit_left :
      (ι ∘ (NatTrans_id F ∘_h (monad_unit Gmon)))%nattrans =
      ((monad_unit Gmon) ∘_h NatTrans_id F)%nattrans;
    distr_law_unit_right :
      (ι ∘ ((monad_unit Fmon) ∘_h NatTrans_id G))%nattrans =
      (NatTrans_id G ∘_h (monad_unit Fmon))%nattrans;
    distr_law_mult_left :
      (ι ∘ (NatTrans_id F ∘_h monad_mult Gmon))%nattrans =
      ((monad_mult Gmon ∘_h NatTrans_id F) ∘
       NatTrans_Functor_assoc_sym F G G ∘ (NatTrans_id G ∘_h ι) ∘
       NatTrans_Functor_assoc G F G ∘
       (ι ∘_h NatTrans_id G) ∘ NatTrans_Functor_assoc_sym G G F)%nattrans;
    distr_law_mult_right :
      (ι ∘ (monad_mult Fmon ∘_h NatTrans_id G))%nattrans =
      ((NatTrans_id G ∘_h monad_mult Fmon) ∘
       NatTrans_Functor_assoc F F G ∘ (ι ∘_h NatTrans_id F) ∘
       NatTrans_Functor_assoc_sym F G F ∘
       (NatTrans_id F ∘_h ι) ∘ NatTrans_Functor_assoc G F F)%nattrans
  }.

  Definition monad_comp_unit : (Functor_id C --> G ∘ F)%nattrans :=
    monad_unit Gmon ∘_h monad_unit Fmon.

  Definition monad_comp_mult : ((G ∘ F) ∘ (G ∘ F) --> G ∘ F)%nattrans :=
    (monad_mult Gmon ∘_h monad_mult Fmon) ∘
    NatTrans_Functor_assoc_sym (F ∘ F) G G ∘
    (NatTrans_id G ∘_h NatTrans_Functor_assoc F F G) ∘
    (NatTrans_id G ∘_h ι ∘_h NatTrans_id F) ∘
    (NatTrans_id G ∘_h NatTrans_Functor_assoc_sym F G F) ∘
    NatTrans_Functor_assoc (G ∘ F) F G.

  Tactic Notation "change_rhs" uconstr(h) :=
    let morph := fresh in
    epose h as morph; transitivity morph; unfold morph; clear morph;
    [solve [rewrite !assoc_sym; repeat f_equal; rewrite !assoc; reflexivity|
            rewrite !assoc; repeat f_equal; rewrite !assoc; reflexivity]|].

  Program Definition monad_comp (dw : distributive_law) : Monad (G ∘ F) :=
    {| monad_unit := monad_comp_unit;
       monad_mult := monad_comp_mult; |}.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    Functor_Simplify; simpl_ids.
    pose proof
         (equal_f_dep (f_equal Trans (distr_law_unit_right dw)) (F _o c)%object)
      as Hright.
    revert Hright; simpl; Functor_Simplify; simpl_ids; intros Hright.
    change_rhs (_ ∘ _ ∘ (((G _a) (Trans ι ((F _o) c))) ∘
           (G _a) (Trans (monad_unit Fmon) ((G _o) ((F _o) c)))) ∘ _)%morphism.
    rewrite <- F_compose.
    cbn; rewrite Hright.
    change_rhs (_ ∘ (Trans (monad_mult Gmon) ((F _o) ((F _o) c)) ∘
               (G _a) ((G _a) (Trans (monad_unit Fmon) ((F _o) c)))) ∘ _)%morphism.
    cbn_rewrite (@Trans_com _ _ _ _ (monad_mult Gmon)).
    cbn.
    rewrite !assoc.
    pose proof (equal_f_dep (f_equal Trans (monad_unit_mult_left Gmon))
                            (F _o c)%object) as Hleft.
    revert Hleft; simpl; Functor_Simplify; simpl_ids; intros Hleft.
    rewrite Hleft; simpl_ids; clear Hleft.
    rewrite <- F_compose.
    pose proof (equal_f_dep (f_equal Trans (monad_unit_mult_left Fmon)) c)
      as Hleft.
    revert Hleft; simpl; Functor_Simplify; simpl_ids; intros Hleft.
    rewrite Hleft; Functor_Simplify; trivial.
  Qed.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    cbn_rewrite (@Trans_com_sym _ _ _ _ (monad_unit Gmon)).
    Functor_Simplify; simpl_ids.
    pose proof
         (equal_f_dep (f_equal Trans (distr_law_unit_left dw)) (F _o c)%object)
      as Hleft.
    revert Hleft; simpl; Functor_Simplify; simpl_ids; intros Hleft.
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ (((G _a) (Trans ι ((F _o) c))) ∘
                    (G _a) ((F _a) (Trans (monad_unit Gmon) ((F _o) c)))) ∘
           _)%morphism.
    rewrite <- F_compose.
    cbn; rewrite Hleft.
    change_rhs (_ ∘ (Trans (monad_mult Gmon) ((F _o) ((F _o) c)) ∘
                (G _a) (Trans (monad_unit Gmon) ((F _o) ((F _o) c)))) ∘ _)%morphism.
    pose proof (equal_f_dep (f_equal Trans (monad_unit_mult_right Gmon))
                            (F _o (F _o c))%object) as Hright.
    revert Hright; simpl; simpl_ids; intros Hright.
    rewrite Hright; simpl_ids; clear Hright.
    rewrite <- F_compose.
    pose proof (equal_f_dep (f_equal Trans (monad_unit_mult_right Fmon)) c)
      as Hright.
    revert Hright; simpl; simpl_ids; intros Hright.
    rewrite Hright; Functor_Simplify; trivial.
  Qed.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    Functor_Simplify; simpl_ids.
    rewrite !F_compose.
    pose proof
         (equal_f_dep (f_equal Trans (distr_law_mult_right dw)) (F _o c)%object)
      as Hright.
    revert Hright; simpl; Functor_Simplify; simpl_ids; intros Hright.
    change_rhs (_ ∘ _ ∘ ((G _a) (Trans ι ((F _o) c)) ∘
                (G _a) (Trans (monad_mult Fmon) ((G _o) ((F _o) c)))) ∘ _)%morphism.
    rewrite <- F_compose.
    cbn; rewrite Hright.
    pose proof (equal_f_dep (f_equal Trans (monad_mult_assoc Fmon)) c) as HassF.
    revert HassF; simpl; Functor_Simplify; simpl_ids; intros HassF.
    rewrite F_compose.
    change_rhs (_ ∘ (Trans (monad_mult Gmon) ((F _o) ((F _o) c)) ∘
                    ((G _a) ((G _a) (Trans (monad_mult Fmon) ((F _o) c))))) ∘ _)%morphism.
    cbn_rewrite (@Trans_com _ _ _ _ (monad_mult Gmon)).
    rewrite !assoc_sym, <- !F_compose.
    cbn; rewrite HassF; clear HassF.
    rewrite !F_compose.
    change_rhs (_ ∘ (((G _a) ((F _a) (Trans (monad_mult Fmon) c))) ∘
                Trans (monad_mult Gmon) ((F _o) ((F _o) ((F _o) c)))) ∘ _)%morphism.
    cbn.
    cbn_rewrite (@Trans_com_sym
                   _ _ _ _ (monad_mult Gmon)
                   _ _ ((F _a) (Trans (monad_mult Fmon) c))%morphism).
    change_rhs (_ ∘ _ ∘ ((G _a) ((G _a) ((F _a) (Trans (monad_mult Fmon) c))) ∘
                (G _a) (Trans ι ((F _o) ((F _o) c)))) ∘ _)%morphism.
    rewrite <- F_compose.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ ι).
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ _ ∘ _ ∘ ((G _a) ((F _a) (Trans ι ((F _o) c)))
         ∘ Trans (monad_mult Gmon) ((F _o) ((F _o) ((G _o) ((F _o) c))))) ∘ _)%morphism.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ (monad_mult Gmon)).
    change_rhs (_ ∘ _ ∘ _ ∘ ((G _a) ((F _a) ((G _a) (Trans (monad_mult Fmon) c)))
         ∘ Trans (monad_mult Gmon) ((F _o) ((G _o) ((F _o) ((F _o) c))))) ∘ _)%morphism.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ (monad_mult Gmon)).
    change_rhs (_ ∘ _ ∘ ((G _a) (Trans ι ((F _o) c)) ∘
                    Trans (monad_mult Gmon) ((F _o) ((G _o) ((F _o) c)))) ∘ _)%morphism.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ (monad_mult Gmon)).
    pose proof (equal_f_dep (f_equal Trans (monad_mult_assoc Gmon))
                            (F _o (F _o c))%object) as HassG.
    revert HassG; simpl; Functor_Simplify; simpl_ids; intros HassG.
    change_rhs (_ ∘ (Trans (monad_mult Gmon) ((F _o) ((F _o) c)) ∘
                     Trans (monad_mult Gmon) ((G _o) ((F _o) ((F _o) c)))) ∘ _)%morphism.
    cbn; rewrite HassG; clear HassG.
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ _ ∘ ((G _a) ((G _a) (Trans ι ((F _o) c))) ∘
      (G _a) ((G _a) ((F _a) ((G _a) (Trans (monad_mult Fmon) c))))) ∘ _)%morphism.
    cbn_rewrite_back (@F_compose _ _ (G ∘ G)).
    cbn; cbn_rewrite (@Trans_com _ _ _ _ ι).
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ ((G _a) (Trans (monad_mult Gmon) ((F _o) ((F _o) c))) ∘
                (G _a) ((G _a) ((G _a) ((F _a) (Trans (monad_mult Fmon) c)))))
                ∘ _)%morphism.
    rewrite <- !F_compose.
    cbn; cbn_rewrite (@Trans_com _ _ _ _ (monad_mult Gmon)).
    rewrite !assoc.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ ι).
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ _ ∘
                ((G _a) (Trans (monad_mult Gmon) ((F _o) ((F _o) ((F _o) c)))) ∘
                 (G _a) ((G _a) (Trans ι ((F _o) ((F _o) c)))) ∘
                 (G _a) (Trans ι ((G _o) ((F _o) ((F _o) c))))) ∘ _)%morphism.
    rewrite <- !F_compose.
    pose proof
         (equal_f_dep (f_equal Trans (distr_law_mult_left dw)) (F _o (F _o c))%object)
      as Hleft.
    revert Hleft; simpl; Functor_Simplify; simpl_ids; intros Hleft.
    rewrite <- Hleft.
    rewrite !F_compose.
    change_rhs (_ ∘ _ ∘ ((G _a) ((G _a) ((F _a) (Trans (monad_mult Fmon) c))) ∘
                     ((G _a) (Trans ι ((F _o) ((F _o) c))))) ∘ _)%morphism.
    rewrite <- !F_compose.
    cbn; cbn_rewrite (@Trans_com_sym _ _ _ _ ι).
    rewrite !F_compose, !assoc; trivial.
  Qed.

End distributive_law.
