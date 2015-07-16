Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func.
Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations
        Ext_Cons.Prod_Cat.Nat_Facts.
Require Import Adjunction.Adjunction.
Require Import KanExt.Local
        KanExt.LocalFacts.HomToCones
        KanExt.LocalFacts.ConesToHom
        KanExt.LocalFacts.Uniqueness.
Require Import Basic_Cons.Terminal.
Require Import Cat.Cat.

Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

(** This module contains facts about local kan extensions involving natural isomorphisms. *)

(** Any two naturally isomorphic functors have the same kan extensions –
stated with hom functor definition of local kan extensions. *)
Section Hom_Local_Right_KanExt_Iso.
  Context {C C' : Category} {p : Functor C C'}
          {D : Category} {F F' : Functor C D}
          (N : (F' ≡≡ F ::> Func_Cat _ _)%morphism)
          (hlrke : Hom_Local_Right_KanExt p F).

  Definition Hom_Local_Right_KanExt_Iso : Hom_Local_Right_KanExt p F' :=
    {|
      HLRKE := hlrke;
      HLRKE_Iso :=
        Isomorphism_Compose
          (NatIso_hor_comp
             (NatTrans_id_Iso (Left_Functor_Extender p D)^op)
             (Fix_Bi_Func_2_object_NatIso (Hom_Func (Func_Cat C D)) N)
          )
          (HLRKE_Iso hlrke)
    |}.

End Hom_Local_Right_KanExt_Iso.

(** Any two naturally isomorphic functors have the same kan extensions –
stated with cones definition of local kan extensions. *)
Section Local_Right_KanExt_Iso.
  Context {C C' : Category}
          {p : Functor C C'}
          {D : Category}
          {F F' : Functor C D}
          (N : (F' ≡≡ F ::> Func_Cat _ _)%morphism)
          (hlrke : Local_Right_KanExt p F).

  Definition Local_Right_KanExt_Iso : Local_Right_KanExt p F' :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (Hom_Local_Right_KanExt_Iso
         N
         (Local_Right_KanExt_to_Hom_Local_Right_KanExt hlrke)
      ).

End Local_Right_KanExt_Iso.

(** If a functor is naturally isomorphic to the local right kan extension then
it also is local right kan extensions *)
Section Iso_Hom_Local_Right_KanExt.
  Context {C C' : Category}
          {p : Functor C C'}
          {D : Category}
          {F : Functor C D}
          {hlrke hlrke' : Functor C' D}
          (N : (hlrke ≡≡ hlrke' ::> Func_Cat _ _)%morphism)
          (ihlrke : Hom_Local_Right_KanExt_Isomorphism p F hlrke).
  
  Definition Iso_Hom_Local_Right_KanExt : Hom_Local_Right_KanExt p F :=
    {|
      HLRKE := hlrke';
      HLRKE_Iso :=
        Isomorphism_Compose
          ihlrke
          (Fix_Bi_Func_2_object_NatIso (Hom_Func (Func_Cat C' D)) N)
    |}.

End Iso_Hom_Local_Right_KanExt.

(** If a functor is naturally isomorphic to the local left kan extension then
it also is local left kan extensions – proven using duality. *)
Section Iso_Local_Right_KanExt.
  Context {C C' : Category}
          {p : Functor C C'}
          {D : Category}
          {F : Functor C D}
          {hlrke hlrke' : Functor C' D}
          (N : (hlrke ≡≡ hlrke' ::> Func_Cat _ _)%morphism)
          (ihlrke : is_Local_Right_KanExt p F hlrke).

  Definition  Iso_Local_Right_KanExt : is_Local_Right_KanExt p F hlrke' :=
    Local_Right_KanExt_is_Local_Right_KanExt
      _
      _
      (
        Hom_Local_Right_KanExt_to_Local_Right_KanExt
          (Iso_Hom_Local_Right_KanExt
             N
             (HLRKE_Iso
                (Local_Right_KanExt_to_Hom_Local_Right_KanExt
                   (is_Local_Right_KanExt_Local_Right_KanExt _ _ ihlrke)
                )
             )
          )
      ).

End Iso_Local_Right_KanExt.


(** Kan extension along any two naturally isomorphic functors is the same –
stated with hom functor definition of local kan extensions. *)
Section Hom_Local_Right_KanExt_Iso_along.
  Context {C C' : Category} {p p' : Functor C C'}
          (N : (p' ≡≡ p ::> Func_Cat _ _)%morphism)
          {D : Category} {F : Functor C D}
          (hlrke : Hom_Local_Right_KanExt p F).

  Program Definition Hom_Local_Right_KanExt_Iso_along : Hom_Local_Right_KanExt p' F :=
    {|
      HLRKE := hlrke;
      HLRKE_Iso :=
        (
          Isomorphism_Compose
            (NatIso_hor_comp
               (Opposite_NatIso (Left_Functor_Extender_Iso N D))
               (NatTrans_id_Iso (@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D))))
            )
            (HLRKE_Iso hlrke))
    |}.

End Hom_Local_Right_KanExt_Iso_along.

(** Any two naturally isomorphic functors have the same kan extensions –
stated with cones definition of local kan extensions. *)
Section Local_Right_KanExt_Iso_along.
  Context {C C' : Category} {p p' : Functor C C'}
          (N : (p' ≡≡ p ::> Func_Cat _ _)%morphism)
          {D : Category} {F : Functor C D}
          (hlrke : Local_Right_KanExt p F).

  Definition Local_Right_KanExt_Iso_along : Local_Right_KanExt p' F :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (Hom_Local_Right_KanExt_Iso_along
         N
         (Local_Right_KanExt_to_Hom_Local_Right_KanExt hlrke)
      ).

End Local_Right_KanExt_Iso_along.


(** Given I : C ≡ D for C and D categories we have KanExt (p ∘ I) (F ∘ I) if we have KanExt p F. *)
Section KanExt_From_Isomorphic_Cat.
  Context {C D : Category}
          (I : (C ≡≡ D ::> Cat)%morphism)
          {D' : Category}
          (p : Functor D D')
          {E : Category}
          (F : Functor D E)
  .

  Section LoKan_Cone_Conv.
    Context (Cn : LoKan_Cone p F).
    
    Program Definition LoKan_Cone_Conv :
      LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))
      :=
        {|
          cone_apex := Cn;
          cone_edge :=
            (
              (
                (cone_edge Cn) ∘_h (NatTrans_id (iso_morphism I))
              )
                ∘ (NatTrans_Functor_assoc_sym _ _ _)
            )%nattrans
        |}
    .

  End LoKan_Cone_Conv.

  Section LoKan_Cone_Conv_back.
    Context (Cn : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))).
    
    Program Definition LoKan_Cone_Conv_back :
      LoKan_Cone p F
      :=
        {|
          cone_apex := Cn;
          cone_edge :=
            (
              (IsoCat_NatTrans I F)
                ∘ (
                  (
                    (NatTrans_Functor_assoc _ _ _)
                      ∘ (
                        (Cn ∘ (NatTrans_Functor_assoc _ _ _))
                          ∘_h NatTrans_id (I ⁻¹)%morphism
                      )
                  )
                    ∘ (NatTrans_Functor_assoc_sym _ _ _)
                )
                ∘ IsoCat_NatTrans_back I (Cn ∘ p))%nattrans
        |}
    .
      
  End LoKan_Cone_Conv_back.

  Section LoKan_Cone_Moprh_to_Conv_back_and_forth.
    Context (Cn : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))).
    
    Program Definition LoKan_Cone_Moprh_to_Conv_back_and_forth :
      LoKan_Cone_Morph Cn (LoKan_Cone_Conv (LoKan_Cone_Conv_back Cn))
      :=
        {|
          cone_morph := NatTrans_id Cn
        |}
    .

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn.
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|- _ = ((match ?e with _ => _ end) ∘ _ ∘ (match ?e with _ => _ end))%morphism] =>
        generalize e
      end.
      intros e.
      set (z := ((I ⁻¹ _o) (((iso_morphism I) _o) x))%object%morphism) in *.
      clearbody z.
      cut (x = z).
      intros H.
      destruct H.
      match goal with
        [|- _ = (?A ∘ _ ∘ ?B)%morphism] =>
        cutrewrite (A = id); [cutrewrite (B = id)|]; try (apply JMeq_eq; destruct e; trivial)
      end.
      {
        auto.
      }      
      {
        cbn_rewrite <- (f_equal (fun u => (u _o x)%object) (left_inverse I)).
        cbn_rewrite <- (f_equal (fun u => (u _o z)%object) (left_inverse I)).
        apply f_equal; trivial.
      }
    Qed.
      
  End LoKan_Cone_Moprh_to_Conv_back_and_forth.

  Section LoKan_Cone_Moprh_from_Conv_forth_and_back.
    Context (Cn : LoKan_Cone p F).
    
    Program Definition LoKan_Cone_Moprh_from_Conv_forth_and_back :
      LoKan_Cone_Morph (LoKan_Cone_Conv_back (LoKan_Cone_Conv Cn)) Cn
      :=
        {|
          cone_morph := NatTrans_id Cn
        |}
    .

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn.
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|- ((match ?e with _ => _ end) ∘ _ ∘ (match ?e with _ => _ end))%morphism = _] =>
        destruct e
      end.
      auto.
    Qed.
      
  End LoKan_Cone_Moprh_from_Conv_forth_and_back.
  
  Section LoKan_Cone_Morph_Conv.
    Context {Cn Cn' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn').
    
    Program Definition LoKan_Cone_Morph_Conv :
      LoKan_Cone_Morph (LoKan_Cone_Conv Cn) (LoKan_Cone_Conv Cn')
      :=
        {|
          cone_morph := h
        |}
    .

    Next Obligation.
      apply NatTrans_eq_simplify.
      FunExt; cbn.
      Functor_Simplify.
      simpl_ids.
      cbn_rewrite (f_equal (fun x => Trans x) (cone_morph_com h)).
      auto.
    Qed.      

  End LoKan_Cone_Morph_Conv.

  Section LoKan_Cone_Morph_Conv_back.
    Context {Cn Cn' : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))}
            (h : LoKan_Cone_Morph Cn Cn')
    .
    
    Program Definition LoKan_Cone_Morph_Conv_back :
      LoKan_Cone_Morph (LoKan_Cone_Conv_back Cn) (LoKan_Cone_Conv_back Cn')
      :=
        {|
          cone_morph := h
        |}
    .

    Next Obligation.
      apply NatTrans_eq_simplify.
      FunExt; cbn.
      cbn_rewrite (f_equal (fun x => Trans x) (cone_morph_com h)).
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|-
         ((match ?e with _ => _ end) ∘ _ ∘ (match ?e with _ => _ end))%morphism =
         (((match ?e with _ => _ end) ∘ _ ∘ (match ?e with _ => _ end)) ∘ _)%morphism
        ] =>
        generalize e
      end.
      intros e.
      repeat rewrite assoc.
      match goal with
        [|-
         (?A1 ∘ ?B1 ∘ ?C1 ∘ ?D1)%morphism =
         (?A2 ∘ ?B2 ∘ ?C2 ∘ ?D2)%morphism
        ] =>
        cutrewrite ((C1 ∘ D1)%morphism = (C2 ∘ D2)%morphism); trivial
      end.
      destruct e; auto.
    Qed.

  End LoKan_Cone_Morph_Conv_back.

  Context (L : Local_Right_KanExt p F).

  Program Definition KanExt_From_Isomorphic_Cat :
    Local_Right_KanExt (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I)) :=
    {|
      LRKE := (LoKan_Cone_Conv L);
      LRKE_morph_ex :=
        fun Cn =>
          LoKan_Cone_Morph_compose
            _
            _
            (LoKan_Cone_Moprh_to_Conv_back_and_forth Cn)
            (LoKan_Cone_Morph_Conv (LRKE_morph_ex L (LoKan_Cone_Conv_back Cn)))
    |}
  .                   

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x.
    set (H :=
           f_equal
             (fun w => Trans w x)
             (LRKE_morph_unique
                L
                (LoKan_Cone_Conv_back Cn)
                (
                  LoKan_Cone_Morph_compose
                    _
                    _
                    (LoKan_Cone_Morph_Conv_back h)
                    (LoKan_Cone_Moprh_from_Conv_forth_and_back _)
                )
                (
                  LoKan_Cone_Morph_compose
                    _
                    _
                    (LoKan_Cone_Morph_Conv_back h')
                    (LoKan_Cone_Moprh_from_Conv_forth_and_back _)
                )
             )
        ).
    cbn in H.
    auto.
  Qed.

End KanExt_From_Isomorphic_Cat.