Require Import Category.Main.
Require Import Functor.Main.
Require Import Archetypal.Discr.

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

    Program Instance CoCone_to_CoCone_1 : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map)) :=
      {
        cone_apex := (cone_apex Cn);
        cone_edge := {|Trans := fun c => Trans ((cone_edge Cn)) c |}
      }.

    Next Obligation.
    Proof.
      destruct h.
      apply (@Trans_com _ _ _ _ Cn x x id).
    Qed.

    Next Obligation.
    Proof.
      destruct h.
      apply (@Trans_com_sym _ _ _ _ Cn x x id).
    Qed.

  End CoCone_to_CoCone_1.

  Section CoCone_to_CoCone_2.
    Context (Cn : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)^op) _ (Opposite_Functor (Discr_Func map))).

    Program Instance CoCone_to_CoCone_2 : @LoKan_Cone _ _ (Functor_To_1_Cat (Discr_Cat A)) _ (@Discr_Func C^op _ map) :=
      {
        cone_apex := (cone_apex Cn);
        cone_edge := {|Trans := fun c => Trans ((cone_edge Cn)) c |}
      }.

    Next Obligation.
    Proof.
      destruct h.
      apply (@Trans_com _ _ _ _ Cn x x id).
    Qed.

    Next Obligation.
    Proof.
      destruct h.
      apply (@Trans_com_sym _ _ _ _ Cn x x id).
    Qed.

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
