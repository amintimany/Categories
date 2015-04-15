Require Import Category.Main.
Require Import Functor.Main.
Require Import Ext_Cons.Arrow.
Require Import Basic_Cons.Terminal.
Require Import Basic_Cons.Equalizer.
Require Import Basic_Cons.Facts.Equalizer_Monic.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import Archetypal.Discr.

Require Import Limits.GenProd_GenSum.
Require Import Limits.Limit.

Section GenProd_Eq_Complete.
  Context {C : Category}.

  Section GenProd_Eq_Limits.
    Context {J : Category}.

    Context {OProd : ∀ (map : J → C), GenProd map} {HProd : ∀ (map : (Arrow J) → C), GenProd map} {Eqs : Has_Equalizers C}.

    Section Limits_Exist.
      Context (D : Functor J C).

      Local Notation DTarg := (fun f => D _o (Targ f)) (only parsing).
      Local Notation DF := Discr_Func (only parsing).
      Local Notation OPR := (OProd (D _o)) (only parsing).
      Local Notation HPR := (HProd DTarg) (only parsing).

      Program Instance Projs_Cone : Cone (DF DTarg) :=
        {|
          cone_apex := Const_Func 1 (OPR _o tt);
          cone_edge := {|Trans := fun f => Trans (cone_edge OPR) (Targ f)|}
        |}.
      
      Definition Projs : Hom C OPR HPR := Trans (LRKE_morph_ex HPR Projs_Cone) tt.

      Program Instance D_imgs_Cone : Cone (DF DTarg) :=
        {|
          cone_apex := Const_Func 1 (OPR _o tt);
          cone_edge := {|Trans := fun f => D _a _ _ (Arr f) ∘ (Trans (cone_edge OPR) (Orig f))|}
        |}.

      Definition D_imgs : Hom C OPR HPR := Trans (LRKE_morph_ex HPR D_imgs_Cone) tt.

      Program Instance Lim_Cone : Cone D :=
        {|
          cone_apex := Const_Func 1 (Eqs _ _ Projs D_imgs);
          cone_edge := {|Trans := fun d => (Trans (cone_edge OPR) d) ∘ (equalizer_morph (Eqs _ _ Projs D_imgs))|}
        |}.

      Next Obligation.
      Proof.
        simpl_ids.
        set (W := f_equal (fun t : NatTrans
                                     (Functor_compose (Functor_To_1_Cat (Discr_Cat (Arrow J)))
                                                      (Const_Func 1 (((OProd (D _o)) _o) tt)))
                                     (DF DTarg) => (Trans t {|Arr := h|}) ∘ (equalizer_morph (Eqs _ _ Projs D_imgs))) (cone_morph_com (LRKE_morph_ex HPR D_imgs_Cone))).
        set (W' := f_equal (fun t : NatTrans
                                      (Functor_compose (Functor_To_1_Cat (Discr_Cat (Arrow J)))
                                                       (Const_Func 1 (((OProd (D _o)) _o) tt)))
                                      (DF DTarg) => Trans t {|Arr := h|} ∘ (equalizer_morph (Eqs _ _ Projs D_imgs))) (cone_morph_com (LRKE_morph_ex HPR Projs_Cone))).
        clearbody W W'.
        rewrite (assoc_sym _ _ ((D _a) c c' h)).
        cbn in *.
        fold D_imgs in W.
        fold Projs in W'.
        rewrite W'.
        etransitivity; [|symmetry; apply W].
        clear W W'.
        repeat rewrite assoc.
        apply (f_equal (fun f => compose f (Trans (HProd (λ f : Arrow J, (D _o) (Targ f))) {| Arr := h |} ))).
        apply (f_equal (fun f => compose f (((HProd (λ f : Arrow J, (D _o) (Targ f))) _a) tt tt tt))).
        apply equalizer_morph_com.
      Qed.        

      Next Obligation.
      Proof.
        symmetry.
        apply Lim_Cone_obligation_1.
      Qed.        

      Section Every_Cone_Equalizes.
        Context (Cn : Cone D).
        
        Program Instance Cone_to_DF_DCone : Cone (DF (D _o)) :=
          {|
            cone_apex := Cn;
            cone_edge :=
              @NatTrans_compose _ _
                                (Functor_compose (Functor_To_1_Cat (Discr_Cat J)) Cn)
                                (Discr_Func ((Functor_compose (Functor_To_1_Cat J) Cn) _o)) _
                                {|Trans := fun _ => id |} (Discretize (cone_edge Cn))
          |}.

        Definition From_Cone_to_OPR : Hom C Cn OPR := Trans (LRKE_morph_ex OPR Cone_to_DF_DCone) tt.
        
        Program Instance Cone_to_DF_DTrag_Cone : Cone (DF DTarg) :=
          {|
            cone_apex := Cn;
            cone_edge := {|Trans := fun c => Trans (Discretize (cone_edge Cn)) (Targ c)|}
          |}.

        Program Instance Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1 : Cone_Morph _ Cone_to_DF_DTrag_Cone HPR :=
          {|
            cone_morph :=
              {|Trans :=
                  fun f =>
                    match f as u return (Hom ((Cn _o) u) (_ u))
                    with
                    | tt => Projs ∘ From_Cone_to_OPR
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          repeat match goal with [H : unit |- _] => destruct H end.
          do 2 rewrite From_Term_Cat.
          auto.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x; cbn.
          unfold Projs, From_Cone_to_OPR.
          set (H := f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat (Arrow J))) Projs_Cone) (DF DTarg) => (Trans w x) ∘ (Trans (LRKE_morph_ex (OProd (D _o)) Cone_to_DF_DCone) tt)) (cone_morph_com (LRKE_morph_ex (HProd (λ f : Arrow J, (D _o) (Targ f))) Projs_Cone))); clearbody H; cbn in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          set (H := f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat J)) Cone_to_DF_DCone) (DF (D _o))=> Trans w (Targ x)) (cone_morph_com (LRKE_morph_ex (OProd (D _o)) Cone_to_DF_DCone))).
          cbn in *.
          rewrite From_Term_Cat in H; simpl_ids in H.
          trivial.
        Qed.

        Program Instance Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2 : Cone_Morph _ Cone_to_DF_DTrag_Cone HPR :=
          {|
            cone_morph :=
              {|Trans :=
                  fun f =>
                    match f as u return (Hom ((Cn _o) u) (_ u))
                    with
                    | tt => D_imgs ∘ From_Cone_to_OPR
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          repeat match goal with [H : unit |- _] => destruct H end.
          do 2 rewrite From_Term_Cat; simpl_ids; trivial.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x.
          cbn.
          unfold D_imgs, From_Cone_to_OPR.
          set (H := f_equal (fun w : NatTrans
                                       (Functor_compose (Functor_To_1_Cat (Discr_Cat (Arrow J))) D_imgs_Cone) (DF DTarg) => (Trans w x) ∘ (Trans (LRKE_morph_ex (OProd (D _o)) Cone_to_DF_DCone) tt)) (cone_morph_com (LRKE_morph_ex (HProd (λ f : Arrow J, (D _o) (Targ f))) D_imgs_Cone))); clearbody H; cbn in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          set (H := f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat J)) Cone_to_DF_DCone) (DF (D _o)) => ((D _a) (Orig x) (Targ x) (Arr x)) ∘ (Trans w (Orig x))) (cone_morph_com (LRKE_morph_ex (OProd (D _o)) Cone_to_DF_DCone))); clearbody H; cbn in H.
          rewrite From_Term_Cat in H; simpl_ids in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          set (W := @Trans_com _ _ _ _ Cn); cbn in W; rewrite <- W; clear W.
          rewrite From_Term_Cat; auto.
        Qed.
        
        Lemma From_Cone_to_Obj_Prod_Equalizes : Projs ∘ From_Cone_to_OPR = D_imgs ∘ From_Cone_to_OPR.
        Proof.
          match goal with
            [|- ?A = ?B] =>
            change A with (Trans Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1 tt);
              change B with (Trans Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2 tt)
          end.
          match goal with
            [|- Trans ?A tt = Trans ?B tt] =>
            cutrewrite (A = B); trivial
          end.
          apply (LRKE_morph_unique HPR).
        Qed.

        Definition From_Cone_to_Lim_Cone : Hom C Cn Lim_Cone :=
          equalizer_morph_ex _  From_Cone_to_Obj_Prod_Equalizes.

        Program Instance Cone_Morph_to_Lim_Cone : Cone_Morph D Cn Lim_Cone :=
          {|
            cone_morph := {|Trans := fun c => match c as u return Hom (Cn _o u) _ with tt => From_Cone_to_Lim_Cone end|}
          |}.

        Next Obligation.
        Proof.
          repeat match goal with [H : unit |- _] => destruct H end.
          rewrite From_Term_Cat; auto.
        Qed.          

        Next Obligation.
          symmetry.
          apply Cone_Morph_to_Lim_Cone_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x.
          unfold From_Cone_to_Lim_Cone.
          cbn in *.
          set (H := equalizer_morph_ex_com (Eqs _ _ Projs D_imgs) From_Cone_to_Obj_Prod_Equalizes); clearbody H; cbn in H.
          simpl_ids.
          rewrite assoc.
          match goal with
            [|- _ = ?A ∘ ?B] =>
            replace B with From_Cone_to_OPR
          end.
          clear H.
          unfold From_Cone_to_OPR.
          set (H := f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat (Discr_Cat J)) Cone_to_DF_DCone) (DF (D _o)) => Trans w x) (cone_morph_com (LRKE_morph_ex (OProd (D _o)) Cone_to_DF_DCone))).
          cbn in H.
          rewrite From_Term_Cat in H; simpl_ids in H.
          trivial.
        Qed.          

      End Every_Cone_Equalizes.

      Section Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR.
        Context {Cn : Cone D} (h : Cone_Morph _ Cn Lim_Cone).

        Program Instance Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR : Cone_Morph _ (Cone_to_DF_DCone Cn) OPR :=
          {|
            cone_morph :=
              {|
                Trans :=
                  fun c =>
                    match c as u return (Hom ((Cn _o) u) (((OProd (D _o)) _o) u)) with
                    | tt => equalizer_morph (Eqs _ _ Projs D_imgs) ∘ Trans h tt
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          repeat match goal with [H : unit |- _] => destruct H end.
          rewrite From_Term_Cat; auto.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR_obligation_1.
        Qed.          

        Next Obligation.
        Proof.        
          apply NatTrans_eq_simplify.
          extensionality x.
          cbn.
          set (H := f_equal (fun w : NatTrans (Functor_compose (Functor_To_1_Cat J) Cn) D => Trans w x) (cone_morph_com h)).
          cbn in H.
          simpl_ids in H.
          rewrite From_Term_Cat; simpl_ids.
          rewrite assoc in H.
          trivial.
        Qed.          

      End Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR.

      Local Notation CMCOPR := Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR (only parsing).

      Program Instance Lim_Cone_is_Limit : Limit D :=
        {|
          LRKE := Lim_Cone;
          LRKE_morph_ex := Cone_Morph_to_Lim_Cone
        |}.

      Next Obligation.
      Proof.
        set (H := LRKE_morph_unique (OProd (D _o)) _ (CMCOPR h) (CMCOPR h')).
        apply (f_equal (fun w : NatTrans (Cone_to_DF_DCone Cn) (OProd (D _o)) => Trans w tt)) in H.
        cbn in H.
        apply NatTrans_eq_simplify.
        extensionality x; destruct x.
        apply (@mono_morphism_monomorphic _ _ _ (@Equalizer_Monic _ _ _ _ _ (Eqs _ _ Projs D_imgs))).
        trivial.
      Qed.        

    End Limits_Exist.
  End GenProd_Eq_Limits.

  Section Restricted_Limits.
    Context (P : Card_Restriction) {CHRP : ∀ (A : Type) (map : A → C), (P A) → GenProd map} {HE : Has_Equalizers C}.

    Instance Restr_GenProd_Eq_Restr_Limits : Has_Restr_Limits C P :=
      fun J D PJ PA => @Lim_Cone_is_Limit J (fun map => CHRP J map PJ) (fun map => CHRP (Arrow J) map PA) HE D.
    
  End Restricted_Limits.

  Section Complete.
    Context {CHAP : ∀ (A : Type) (map : A → C), GenProd map} {HE : Has_Equalizers C}.
    
    Instance GenProd_Eq_Complete : Complete C := fun J => Local_to_Global_Right _ _ (fun D => @Lim_Cone_is_Limit J (CHAP J) (CHAP (Arrow J)) HE D).
    
  End Complete.

End GenProd_Eq_Complete.

Section GenSum_CoEq_Complete.
  Context {C : Category}.

  Section GenSum_CoEq_CoLimits.
    Context {J : Category}.

    Context {OSum : ∀ (map : J → C), GenSum map} {HSum : ∀ (map : (Arrow J) → C), GenSum map} {Eqs : Has_CoEqualizers C}.

    Section Limits_Exist.
      Context (D : Functor J C).

      Instance CoLim_CoCone_is_CoLimit : CoLimit D := @Lim_Cone_is_Limit C^op J^op (fun map => GenSum_to_GenProd (OSum map)) (fun map => GenSum_to_GenProd (@GenSum_IsoType _ _ (Arrow_OP_Iso J) _ HSum map)) Eqs (Opposite_Functor D).
      
    End Limits_Exist.
  End GenSum_CoEq_CoLimits.

  Section Restricted_CoLimits.
    Context (P : Card_Restriction) {CHRP : ∀ (A : Type) (map : A → C), (P A) → GenSum map} {HE : Has_CoEqualizers C}.
    
    Instance Restr_GenSum_CoEq_Restr_CoLimits : Has_Restr_CoLimits C P :=
      fun J D PJ PA => @CoLim_CoCone_is_CoLimit J (fun map => CHRP J map PJ) (fun map => CHRP (Arrow J) map PA) HE D.
    
  End Restricted_CoLimits.

  Section CoComplete.
    Context {CHAP : ∀ (A : Type) (map : A → C), GenSum map} {HE : Has_CoEqualizers C}.
    
    Instance GenSum_CoEq_CoComplete : CoComplete C := fun J => Local_to_Global_Left _ _ (fun D => @CoLim_CoCone_is_CoLimit J (CHAP J) (CHAP (Arrow J)) HE D).
    
  End CoComplete.

End GenSum_CoEq_Complete.