Require Import Category.Main.
Require Import Functor.Main.
Require Import Archetypal.Discr.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Require Import Limits.Limit.

Section GenProd_Sum.
  Context {A : Type} {C : Category} (map : A → C).

  SubClass GenProd := Limit (Discr_Func map).

  Existing Class GenProd.
  
  SubClass GenSum := CoLimit (Discr_Func map).

  Existing Class GenSum.

End GenProd_Sum.
  
Section Conversion.
  Context {A : Type} {C : Category} {map : A → C}.
  
  Section CoCone_to_CoCone_1.
    Context (Cn : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)) _ (@Discr_Func C^op _ map)).

    Local Hint Extern 1 => cbn.

    Program Instance CoCone_to_CoCone_1 : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map)) :=
      {
        cone_apex := (cone_apex Cn);
        cone_edge := {|Trans := fun c => Trans ((cone_edge Cn)) c |}
      }.

  End CoCone_to_CoCone_1.

  Section CoCone_to_CoCone_2.
    Context (Cn : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map))).

    Local Hint Extern 1 => cbn.
    
    Program Instance CoCone_to_CoCone_2 : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)) _ (@Discr_Func C^op _ map) :=
      {
        cone_apex := (cone_apex Cn);
        cone_edge := {|Trans := fun c => Trans ((cone_edge Cn)) c |}
      }.

  End CoCone_to_CoCone_2.

  Section CoCone_to_CoCone_1_2.
    Context (Cn : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)) _ (@Discr_Func C^op _ map)).

    Theorem CoCone_to_CoCone_1_2 : CoCone_to_CoCone_2 (CoCone_to_CoCone_1 Cn) = Cn.
    Proof.    
      unfold CoCone_to_CoCone_1, CoCone_to_CoCone_2.
      destruct Cn as [ap ed]; cbn in *.
      match goal with
        [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
      end.
      apply NatTrans_eq_simplify; trivial.
    Qed.
    
  End CoCone_to_CoCone_1_2.

  Section CoCone_to_CoCone_2_1.
    Context (Cn : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map))).

    Theorem CoCone_to_CoCone_2_1 : CoCone_to_CoCone_1 (CoCone_to_CoCone_2 Cn) = Cn.
    Proof.    
      unfold CoCone_to_CoCone_1, CoCone_to_CoCone_2.
      destruct Cn as [ap ed]; cbn in *.
      match goal with
        [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
      end.
      apply NatTrans_eq_simplify; trivial.
    Qed.
    
  End CoCone_to_CoCone_2_1.
  
  Section CoCone_Morph_to_CoCone_Morph_1.
    Context {Cn Cn' : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)) _ (@Discr_Func C^op _ map)}
            (h : LoKan_Cone_Morph Cn Cn').

    Program Instance CoCone_Morph_to_CoCone_Morph_1 : LoKan_Cone_Morph (CoCone_to_CoCone_1 Cn) (CoCone_to_CoCone_1 Cn') :=
      {
        cone_morph := cone_morph h
      }.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; apply (f_equal Trans (cone_morph_com h)).
    Qed.

  End CoCone_Morph_to_CoCone_Morph_1.

  Section CoCone_Morph_to_CoCone_Morph_2.
    Context {Cn Cn' : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map))}
            (h : LoKan_Cone_Morph Cn Cn').

    Program Instance CoCone_Morph_to_CoCone_Morph_2 : LoKan_Cone_Morph (CoCone_to_CoCone_2 Cn) (CoCone_to_CoCone_2 Cn') :=
      {
        cone_morph := cone_morph h
      }.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; apply (f_equal Trans (cone_morph_com h)).
    Qed.

  End CoCone_Morph_to_CoCone_Morph_2.

End Conversion.

Section GenProd_to_GenSum.
  Context {A : Type} {C : Category} {map : A → C} (L : GenProd map).
  
  Program Instance GenProd_to_GenSum : @GenSum A C^op map :=
    {|
      LRKE := @CoCone_to_CoCone_1 _ C^op _ (LRKE L)
    |}.
  
  Next Obligation.
  Proof.
    set (W := @CoCone_Morph_to_CoCone_Morph_1 _ C^op map _ _ (LRKE_morph_ex L (@CoCone_to_CoCone_2 _ C^op map Cn))).
    rewrite CoCone_to_CoCone_2_1 in W.
    exact W.
  Defined.

  Next Obligation.
  Proof.
    set (Wh := CoCone_Morph_to_CoCone_Morph_2 h).
    set (Wh' := CoCone_Morph_to_CoCone_Morph_2 h').
    set (M := LRKE_morph_unique L).
    rewrite <- (@CoCone_to_CoCone_1_2 _ C^op _ (LRKE L)) in M.
    set (M' := M _ Wh Wh').
    change (cone_morph h) with (cone_morph Wh).
    change (cone_morph h') with (cone_morph Wh').
    destruct M; trivial.
  Qed.

End GenProd_to_GenSum.

Section GenSum_to_GenProd.
  Context {A : Type} {C : Category} {map : A → C} (L : GenSum map).
  
  Program Instance GenSum_to_GenProd : @GenProd A C^op map :=
    {|
      LRKE := @CoCone_to_CoCone_2 _ C _ (LRKE L)
    |}.
  
  Next Obligation.
  Proof.
    set (W := @CoCone_Morph_to_CoCone_Morph_2 _ C map _ _ (LRKE_morph_ex L (@CoCone_to_CoCone_1 _ C map Cn))).
    rewrite CoCone_to_CoCone_1_2 in W.
    exact W.
  Defined.

  Next Obligation.
  Proof.
    set (Wh := CoCone_Morph_to_CoCone_Morph_1 h).
    set (Wh' := CoCone_Morph_to_CoCone_Morph_1 h').
    set (M := LRKE_morph_unique L).
    rewrite <- (@CoCone_to_CoCone_2_1 _ C _ (LRKE L)) in M.
    set (M' := M _ Wh Wh').
    change (cone_morph h) with (cone_morph Wh).
    change (cone_morph h') with (cone_morph Wh').
    destruct M; trivial.
  Qed.

End GenSum_to_GenProd.

Section GenProd_IsoType_Cone_Conversion_1.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} (Cn : Cone (Discr_Func (f ∘ (iso_morphism Iso)))).

  Local Obligation Tactic := idtac.
  
  Program Instance GenProd_IsoType_Cone_Conversion_1 : Cone (Discr_Func f) :=
    {|
      cone_apex := Cn;
      cone_edge :=
        {|
          Trans :=
            fun c =>
              match equal_f (right_inverse Iso) c in _ = u return
                    Hom ((Cn _o) tt) (f u) with
                eq_refl => Trans Cn ((inverse_morphism Iso) c)
              end
        |}
    |}.

  Next Obligation.
  Proof.
    intros c c' h.
    destruct h.
    cbn.
    simpl_ids; auto.
  Qed.

  Next Obligation.
  Proof.  
    symmetry.
    apply GenProd_IsoType_Cone_Conversion_1_obligation_1.
  Qed.    

End GenProd_IsoType_Cone_Conversion_1.
  
Section GenProd_IsoType_Cone_Conversion_2.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} (Cn : Cone (Discr_Func f)).

  Local Obligation Tactic := idtac.
  
  Program Instance GenProd_IsoType_Cone_Conversion_2 : Cone (Discr_Func (f ∘ (iso_morphism Iso))) :=
    {|
      cone_apex := Cn;
      cone_edge :=
        {|
          Trans :=
            fun c =>Trans Cn ((iso_morphism Iso) c)
        |}
    |}.

  Next Obligation.
  Proof.
    intros c c' h.
    destruct h.
    cbn.
    simpl_ids; auto.
  Qed.

  Next Obligation.
  Proof.  
    symmetry.
    apply GenProd_IsoType_Cone_Conversion_2_obligation_1.
  Qed.    

End GenProd_IsoType_Cone_Conversion_2.

Section GenProd_IsoType_Cone_Conversion_1_2.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} (Cn : Cone (Discr_Func (f ∘ (iso_morphism Iso)))).

  Theorem GenProd_IsoType_Cone_Conversion_1_2 : GenProd_IsoType_Cone_Conversion_2 (GenProd_IsoType_Cone_Conversion_1 Cn) = Cn.
  Proof.
    unfold GenProd_IsoType_Cone_Conversion_1, GenProd_IsoType_Cone_Conversion_2.
    destruct Cn.
    cbn.
    match goal with
      [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
    end.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    apply JMeq_eq.
    destruct equal_f.
    set (H := equal_f (left_inverse Iso) c).
    cbn in H.
    rewrite H.
    trivial.
  Qed.

End GenProd_IsoType_Cone_Conversion_1_2.

Section GenProd_IsoType_Cone_Conversion_2_1.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} (Cn : Cone (Discr_Func f)).

  Theorem GenProd_IsoType_Cone_Conversion_2_1 : GenProd_IsoType_Cone_Conversion_1 (GenProd_IsoType_Cone_Conversion_2 Cn) = Cn.
  Proof.
    unfold GenProd_IsoType_Cone_Conversion_1, GenProd_IsoType_Cone_Conversion_2.
    destruct Cn.
    cbn.
    match goal with
      [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
    end.
    apply NatTrans_eq_simplify; extensionality c; cbn.
    destruct equal_f; trivial.
  Qed.

End GenProd_IsoType_Cone_Conversion_2_1.

Section GenProd_IsoType_Cone_Morph_Conversion_1.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} {Cn Cn' : Cone (Discr_Func (f ∘ (iso_morphism Iso)))} (h : Cone_Morph _ Cn Cn').

  Local Obligation Tactic := idtac.
  
  Program Instance GenProd_IsoType_Cone_Morph_Conversion_1 : Cone_Morph (Discr_Func f) (GenProd_IsoType_Cone_Conversion_1 Cn) (GenProd_IsoType_Cone_Conversion_1 Cn') :=
    {|
      cone_morph := h
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    destruct equal_f.
    apply (f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat A)) Cn) (Discr_Func (f ∘ (iso_morphism Iso))) => Trans w (inverse_morphism Iso x)) (cone_morph_com h)).
  Qed.

End GenProd_IsoType_Cone_Morph_Conversion_1.
  
Section GenProd_IsoType_Cone_Morph_Conversion_2.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} {f : B → C} {Cn Cn' : Cone (Discr_Func f)} (h : Cone_Morph _ Cn Cn').

  Local Obligation Tactic := idtac.
  
  Program Instance GenProd_IsoType_Cone_Morph_Conversion_2 : Cone_Morph (Discr_Func (f ∘ (iso_morphism Iso))) (GenProd_IsoType_Cone_Conversion_2 Cn) (GenProd_IsoType_Cone_Conversion_2 Cn') :=
    {|
      cone_morph := h
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply (f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat B)) Cn) (Discr_Func f) => Trans w (iso_morphism Iso x)) (cone_morph_com h)).
  Qed.

End GenProd_IsoType_Cone_Morph_Conversion_2.

Section GenProd_IsoType.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} (H : forall f : A → C, GenProd f).
  
  Local Obligation Tactic := idtac.
  
  Program Instance GenProd_IsoType (map : B → C) : GenProd map :=
    {|
      LRKE := GenProd_IsoType_Cone_Conversion_1 (H (map ∘ (iso_morphism Iso)))
    |}.

  Next Obligation.
  Proof.  
    intros map Cn.
    set (W := GenProd_IsoType_Cone_Morph_Conversion_1 (LRKE_morph_ex (H (map ∘ (iso_morphism Iso))) (GenProd_IsoType_Cone_Conversion_2 Cn))).
    rewrite GenProd_IsoType_Cone_Conversion_2_1 in W.
    exact W.
  Defined.    

  Next Obligation.
  Proof.
    intros map Cn h h'.
    set (Wh := GenProd_IsoType_Cone_Morph_Conversion_2 h).
    set (Wh' := GenProd_IsoType_Cone_Morph_Conversion_2 h').
    set (M := LRKE_morph_unique (H (map ∘ Iso))).
    rewrite <- (@GenProd_IsoType_Cone_Conversion_1_2 _ _ _ _ _ (LRKE (H (map ∘ Iso)))) in M.
    set (M' := M _ Wh Wh').
    change (cone_morph h) with (cone_morph Wh).
    change (cone_morph h') with (cone_morph Wh').
    destruct M; trivial.
  Qed.

End GenProd_IsoType.

Section GenSum_IsoType.
  Context {A B : Type} {Iso : A ≡≡ B ::> Type_Cat} {C : Category} (H : forall f : A → C, GenSum f).
  
  Local Obligation Tactic := idtac.
  
  Instance GenSum_IsoType (map : B → C) : GenSum map.
  Proof.
    apply (@GenProd_to_GenSum B C^op).
    apply GenProd_IsoType.
    clear map.
    intros f.
    apply GenSum_to_GenProd.
    apply H.
  Defined.    

End GenSum_IsoType.