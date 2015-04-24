Require Import Category.Main.
Require Import Functor.Main Functor.Representable.Hom_Func.
Require Import Basic_Cons.Terminal.
Require Import Ext_Cons.Arrow.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Limits.Limit.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import NatTrans.Main.
Require Import Cat.Cat_Terminal.

Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Section Limits_Pointwise.
  Context {J C : Category} (D : Functor J C) (x : C).

  Local Notation REPx := (@Fix_Bi_Func_1 C^op _ _ x (Hom_Func C)) (only parsing).

  Local Notation REPxComp U := (FCOMP U REPx) (only parsing).
  
  Section Limits_Pointwise_Cone_Cov.
    Context (Cn : Cone D).

    Instance Limits_Pointwise_Cone_Cov : Cone (REPxComp D) :=
      {|
        cone_apex := (REPxComp Cn);
        cone_edge := NCOMP (NatTrans_Functor_assoc _ _ _) (HCOMP (cone_edge Cn) (NID REPx))
      |}.

  End Limits_Pointwise_Cone_Cov.

  Local Notation LPCC := Limits_Pointwise_Cone_Cov.

  Section Limits_Pointwise_Cone_Cov_Back.
    Context (Cn : Cone (REPxComp D)) (w : Cn _o tt).

    Program Instance Limits_Pointwise_Cone_Cov_Back : Cone D :=
      {|
        cone_apex := Const_Func Discr.SingletonCat x;
        cone_edge :=  {|Trans := fun c => Trans (cone_edge Cn) c w |}
      |}.

    Next Obligation.
    Proof.
      set (W := equal_f (@Trans_com _ _ _ _ Cn c c' h) w); cbn in W; rewrite From_Term_Cat in W.
      auto.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Limits_Pointwise_Cone_Cov_Back_obligation_1.
    Qed.      

  End Limits_Pointwise_Cone_Cov_Back.

  Local Notation LPCCB := Limits_Pointwise_Cone_Cov_Back.
  
  Section Limits_Pointwise_Cone_Morph_Cov.
    Context {Cn Cn' : Cone D} (h : Cone_Morph D Cn Cn').

    Program Instance Limits_Pointwise_Cone_Morph_Cov : Cone_Morph (REPxComp D) (LPCC Cn) (LPCC Cn') :=
      {|
        cone_morph := HCOMP (cone_morph h) (NID REPx)
      |}.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality f; extensionality y.
      set (W := f_equal (fun w : NatTrans (FCOMP (Functor_To_1_Cat J) Cn) D => Trans w f) (cone_morph_com h)); cbn in *; rewrite W.
      auto.
    Qed.
      
  End Limits_Pointwise_Cone_Morph_Cov.

  Local Notation LPCHC := Limits_Pointwise_Cone_Morph_Cov.
  
  Context (L : Limit D).

  Section Limits_Pointwise_Cone_Morph_to_LPCC_Limit.
    Context (Cn : Cone (REPxComp D)).

    Program Instance Limits_Pointwise_Cone_Morph_to_LPCC_Limit : Cone_Morph (REPxComp D) Cn (LPCC L) :=
      {|
        cone_morph :=
          {|
            Trans :=
              fun c w =>
                match c as u return (Cn _o u) → Hom x (L _o u) with
                  tt => fun w => Trans (LRKE_morph_ex L (LPCCB Cn w)) tt
                end w
          |}
      |}.

    Next Obligation.
    Proof.
      extensionality z.
      destruct c.
      destruct c'.
      destruct h.
      repeat rewrite From_Term_Cat; auto.
    Qed.      

    Next Obligation.
    Proof.
      symmetry.
      apply Limits_Pointwise_Cone_Morph_to_LPCC_Limit_obligation_1.
    Qed.    

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality c; extensionality w.
      set (W := f_equal (fun m : NatTrans (FCOMP (Functor_To_1_Cat J) (LPCCB Cn w)) D => Trans m c) (cone_morph_com (LRKE_morph_ex L (LPCCB Cn w)))).
      cbn in *.
      auto.
    Qed.      

  End Limits_Pointwise_Cone_Morph_to_LPCC_Limit.

  Local Notation LPCMTL := Limits_Pointwise_Cone_Morph_to_LPCC_Limit.
  
  Section Limits_Pointwise_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.
    Context {Cn : Cone (REPxComp D)} (h : Cone_Morph (REPxComp D) Cn (LPCC L)) (w : (Cn _o) tt).

    Program Instance Limits_Pointwise_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit : Cone_Morph D (LPCCB Cn w) L :=
      {|
        cone_morph :=
          {|
            Trans :=
              fun c =>
                match c as u return Hom x (L _o u) with
                  tt => Trans h tt w
                end
          |}
      |}.

    Next Obligation.
    Proof.
      destruct c; destruct c'.
      repeat rewrite From_Term_Cat; auto.
    Qed.      

    Next Obligation.
    Proof.
      symmetry.
      apply Limits_Pointwise_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit_obligation_1.
    Qed.    

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality c.
      set (W := f_equal (fun m : NatTrans (FCOMP (Functor_To_1_Cat J) Cn) (REPxComp D) => Trans m c w) (cone_morph_com h)).
      cbn in *.
      auto.
    Qed.      

  End Limits_Pointwise_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.

  Local Notation LPCMTLTL := Limits_Pointwise_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.
  
  Program Instance Limits_Pointwise : Limit (REPxComp D) :=
    {|
      LRKE := LPCC L;
      LRKE_morph_ex := fun Cn => LPCMTL Cn
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality z; extensionality w; destruct z; cbn in *.
    apply (f_equal (fun m :  NatTrans (LPCCB Cn w) L => Trans m tt) (LRKE_morph_unique L _ (LPCMTLTL h w)(LPCMTLTL h' w))).
  Qed.

End Limits_Pointwise.

Section CoLimits_Pointwise.
  Context {J C : Category} (D : Functor J C) (x : C).

  Local Notation REPx := (@Fix_Bi_Func_1 C _ _ x (Hom_Func C^op)) (only parsing).

  Local Notation REPxComp U := (FCOMP U (FOP REPx)) (only parsing).

  Context (L : CoLimit D).

  Instance CoLimits_Pointwise : CoLimit (REPxComp D) := Limits_Pointwise (Opposite_Functor D) x L.

End CoLimits_Pointwise.