Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.

Section KanExtension.
  Context {C C' : Category} (p : Functor C C').

  Local Notation FCOMP := Functor_compose (only parsing).
  Local Notation NCOMP := NatTrans_compose (only parsing).
  Local Notation HCOMP := NatTrans_hor_comp (only parsing).
  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).
  
  Section Global.
    Context (D : Category).
    
    Program Instance GExtend :
      Functor (Func_Cat C' D) (Func_Cat C D) :=
      {
        FO := fun F => FCOMP p F;
        FA := fun F F' N => HCOMP (NID p) N
      }.

    Next Obligation.
      apply NatTrans_eq_simplify.
      extensionality y.
      simpl; auto.
    Qed.      

    Next Obligation.
      apply NatTrans_eq_simplify.
      extensionality y.
      simpl; auto.
    Qed.

    Class GLan : Type :=
      {
        glan : Functor (FCAT C D) (FCAT C' D);
        glan_adj : Adjunct glan GExtend
      }.

    Coercion glan : GLan >-> Functor.

    Class GRan : Type :=
      {
        gran : Functor (FCAT C D) (FCAT C' D);
        gran_adj : Adjunct GExtend gran
      }.

  End Global.

  Section Local.
    Context {D : Category} (F : Functor C D).

    Class Lan : Type :=
      {
        left_ext : Functor C' D;

        left_ext_nt : NatTrans F (FCOMP p left_ext);

        from_left_ext : ∀ (G : Functor C' D) (G_nt : NatTrans F (FCOMP p G)),
            NatTrans left_ext G;

        left_ext_nt_factors : ∀ (G : Functor C' D) (G_nt : NatTrans F (FCOMP p G)),
            G_nt = NCOMP left_ext_nt (HCOMP (NID p) (from_left_ext G G_nt));

        left_ext_nt_factors_uniquely : ∀ (G : Functor C' D) (G_nt : NatTrans F (FCOMP p G)) (N N' : NatTrans left_ext G),
            G_nt = NCOMP left_ext_nt (HCOMP (NID p) N) →
            G_nt = NCOMP left_ext_nt (HCOMP (NID p) N') →
            N = N'
      }.

    Coercion left_ext : Lan >-> Functor.


    Class Ran : Type :=
      {
        right_ext : Functor C' D;

        right_ext_nt : NatTrans (FCOMP p right_ext) F;

        to_right_ext : ∀ (G : Functor C' D) (G_nt : NatTrans (FCOMP p G) F),
            NatTrans G right_ext;

        right_ext_nt_factors : ∀ (G : Functor C' D) (G_nt : NatTrans (FCOMP p G) F),
            G_nt = NCOMP (HCOMP (NID p) (to_right_ext G G_nt)) right_ext_nt;

        right_ext_nt_factors_uniquely : ∀ (G : Functor C' D) (G_nt : NatTrans (FCOMP p G) F) (N N' : NatTrans G right_ext),
            G_nt = NCOMP (HCOMP (NID p) N) right_ext_nt →
            G_nt = NCOMP (HCOMP (NID p) N') right_ext_nt →
            N = N'
      }.

    Coercion right_ext : Ran >-> Functor.
    
  End Local.

End KanExtension.