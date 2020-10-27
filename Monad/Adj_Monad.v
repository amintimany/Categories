From Categories.Essentials Require Import Notations Facts_Tactics.
From Categories.Category Require Import Main.
From Categories.Functor Require Import Functor Functor_Ops.
From Categories.NatTrans Require Import Main.
From Categories.Adjunction Require Import Main.
From Categories.Monad Require Import Monad.

Section Adj_Monad.
  Context {C D : Category} {F : (C --> D)%functor} {U : (D --> C)%functor}
          (adj : (F ⊣ U)%functor).

  Let M := (U ∘ F)%functor.

  Program Definition adj_FU : (F ∘ U --> Functor_id D)%nattrans :=
    {| Trans d := adj_morph_ex adj (id ((U _o) d)%object) |}.
  Next Obligation.
  Proof.
    eapply (adj_morph_unique adj ((U _a)%morphism h)).
    - rewrite F_compose, assoc; cbn.
      cbn_rewrite (Trans_com_sym (adj_unit adj) (U _a h)).
      rewrite assoc_sym.
      cbn_rewrite <- (@adj_morph_com _ _ _ _ adj).
      rewrite id_unit_left; trivial.
    - rewrite F_compose, assoc; cbn.
      cbn_rewrite <- (@adj_morph_com _ _ _ _ adj).
      rewrite id_unit_right; trivial.
  Qed.
  Next Obligation.
  Proof.
    symmetry.
    apply adj_FU_obligation_1.
  Qed.

  Definition adj_mult : (M ∘ M --> M)%nattrans :=
    ((((NatTrans_id U) ∘_h
     ((NatTrans_from_compose_id F) ∘ adj_FU ∘_h (NatTrans_id F))) ∘
     ((NatTrans_id U) ∘_h (NatTrans_Functor_assoc_sym F U F))) ∘
     ((NatTrans_Functor_assoc (U ∘ F) F U)))%nattrans.

  Program Definition adj_monad : Monad M :=
    {| monad_unit := adj_unit adj;
       monad_mult := adj_mult |}.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    Functor_Simplify; simpl_ids.
    cbn_rewrite <- (@adj_morph_com _ _ _ _ adj); trivial.
  Qed.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    Functor_Simplify; simpl_ids.
    rewrite <- F_compose; simpl.
    assert (adj_morph_ex adj id ∘ (F _a)%morphism (Trans (adj_unit adj) c)
            = id)%morphism as Heq.
    - eapply (@adj_morph_unique _ _ _ _ adj);
        [|Functor_Simplify; simpl_ids; reflexivity].
      simpl.
      rewrite F_compose.
      rewrite assoc.
      cbn_rewrite (@Trans_com_sym _ _ _ _ (adj_unit adj)).
      rewrite <- assoc.
      cbn_rewrite_back (@adj_morph_com _ _ _ _ adj).
      replace (id ((U _o) ((F _o) c))) with ((U _a) ((F _a) (id c)))%morphism
      by (Functor_Simplify; trivial).
      cbn_rewrite (@Trans_com_sym _ _ _ _ (adj_unit adj)).
      simpl_ids; trivial.
    - simpl in *; rewrite Heq; Functor_Simplify; trivial.
  Qed.
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    Functor_Simplify; simpl_ids.
    rewrite <- !F_compose.
    f_equal.
    eapply (@adj_morph_unique _ _ _ _ adj); [reflexivity|].
    rewrite !F_compose, !assoc.
    cbn_rewrite (@Trans_com_sym _ _ _ _ (adj_unit adj)).
    cbn_rewrite_back (@adj_morph_com _ _ _ _ adj).
    rewrite <- !assoc.
    cbn_rewrite_back (@adj_morph_com _ _ _ _ adj).
    simpl_ids; trivial.
  Qed.

End Adj_Monad.
