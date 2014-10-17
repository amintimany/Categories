Require Import Category.Main.
Require Import Functor.Main.
Require Import Ext_Cons.Arrow.
Require Import Basic_Cons.Terminal.
Require Import Basic_Cons.General_Product.
Require Import Basic_Cons.Equalizer.
Require Import Basic_Cons.Facts.Equalizer_Monic.
Require Import Coq_Cats.Type_Cat.Card_Restriction.

Require Import Limits.Limit.

Section Gen_Prod_Eq_Complete.
  Context `{C : Category Obj Hom}.

  Section Gen_Prod_Eq_Limits.
    Context `{J : Category Obj' Hom'}.

    Context {HGPO : Has_General_Products C Obj'} {HGPH : Has_General_Products C (Arrow J)} {HE : Has_Equalizers C}.

    Section Limits_Exist.

      Context (D : Functor J C).

      Let Obj_Prod : Obj := Gen_Prod_of (D _o).

      Let Hom_Prod : Obj := Gen_Prod_of (λ f, D _o (Targ f)).

      Let Obj_Prod_prod : General_Product _ _ _ Obj_Prod := @Gen_Prod_prod _ _ _ _ HGPO (D _o).

      Let Hom_Prod_prod : General_Product _ _ _ Hom_Prod := @Gen_Prod_prod _ _ _ _ HGPH (λ f, D _o (Targ f)).

      Definition Projs : Hom Obj_Prod Hom_Prod := (@GP_Prod_morph_ex _ _ _ _ _ _ Hom_Prod_prod Obj_Prod (λ f, @GP_Proj _ _ _ _ _ _ Obj_Prod_prod (Targ f))).

      Definition D_imgs : Hom Obj_Prod Hom_Prod := (@GP_Prod_morph_ex _ _ _ _ _ _ Hom_Prod_prod Obj_Prod (λ f, (D _a _ _ (Arr f)) ∘ (@GP_Proj _ _ _ _ _ _ Obj_Prod_prod (Orig f)))).
      
      Program Instance Lim_Cone : Cone D :=
        {
          Cone_obj := Equalizer_of Projs D_imgs;
          Cone_arrow := λ c, (@GP_Proj _ _ _ _ _ _ Obj_Prod_prod c) ∘ (@equalizer_morph _ _ _ _ _ Projs D_imgs _ (@Equalizer_of_Equalizer _ _ _ HE _ _ Projs D_imgs))
        }.

      Next Obligation. (* Cone_com *)
      Proof.
        rewrite <- assoc.
        match goal with
            [|- ?A ∘ ?C = ?D ∘ ?E] =>
            let H := fresh "H" in
            let H' := fresh "H'" in
            cut (A = @GP_Proj _ _ _ _ _ _ Hom_Prod_prod (@Build_Arrow _ _ _ _ _ h) ∘ D_imgs);
              [cut(D = @GP_Proj _ _ _ _ _ _ Hom_Prod_prod (@Build_Arrow _ _ _ _ _ h) ∘ Projs);
                [intros H H'; rewrite H; rewrite H'; clear H H' | ] |
              ]
        end.
        repeat rewrite assoc.
        rewrite equalizer_morph_com.
        reflexivity.
        {
          unfold Projs.
          rewrite (@GP_Prod_morph_com _ _ _ _ (λ f : Arrow J, (D _o) (Targ f))).
          reflexivity.
        }
        {
          unfold D_imgs.
          rewrite (@GP_Prod_morph_com _ _ _ _ (λ f : Arrow J, (D _o) (Targ f))).
          reflexivity.
        }
      Qed.

      Section Every_Cone_Equalizes.
        Context (cn : Cone D).
        
        Definition From_Cone_to_Obj_Prod : Hom (Cone_obj cn) Obj_Prod := (@GP_Prod_morph_ex _ _ _ _ _ _ Obj_Prod_prod (Cone_obj cn) (Cone_arrow cn)).

        Lemma From_Cone_to_Obj_Prod_Equalizes : Projs ∘ From_Cone_to_Obj_Prod = D_imgs ∘ From_Cone_to_Obj_Prod.
        Proof.
          apply (@GP_Prod_morph_unique _ _ _ _ _ _ Hom_Prod_prod (Cone_obj cn) (λ f, (Cone_arrow cn (Targ f)))); intros f; rewrite <- assoc.
          {
            unfold Projs.
            rewrite (@GP_Prod_morph_com _ _ _ _ (λ f : Arrow J, (D _o) (Targ f))).
            unfold From_Cone_to_Obj_Prod.
            rewrite (@GP_Prod_morph_com _ _ _ _ (D _o)).
            reflexivity.
          }
          {
            unfold D_imgs.
            rewrite (@GP_Prod_morph_com _ _ _ _ (λ f : Arrow J, (D _o) (Targ f))).
            rewrite <- (@Cone_com _ _ _ _ _ _ D cn _ _ (Arr f)).
            rewrite assoc; f_equal.
            unfold From_Cone_to_Obj_Prod.
            rewrite (@GP_Prod_morph_com _ _ _ _ (D _o)).
            reflexivity.
          }
        Qed.

        Definition From_Cone_to_Lim_Cone : Hom (Cone_obj cn) (Cone_obj Lim_Cone) :=
          equalizer_morph_ex _ _ _ _ _ From_Cone_to_Obj_Prod_Equalizes.

        Program Instance Cone_Morph_to_Lim_Cone : Cone_Morph D cn Lim_Cone :=
          {
            Cone_Morph_arrow := From_Cone_to_Lim_Cone
          }.

        Next Obligation. (* Cone_Morph_com *)
        Proof.
          match goal with
              [|- (?A ∘ ?B) ∘ ?C = ?D] =>
              cutrewrite (D = A ∘ From_Cone_to_Obj_Prod)
          end.
          {
            rewrite assoc; f_equal.
            unfold From_Cone_to_Lim_Cone.
            rewrite equalizer_morph_ex_com.
            reflexivity.
          }
          {
            unfold From_Cone_to_Obj_Prod.
            rewrite GP_Prod_morph_com.
            reflexivity.
          }
        Qed.

      End Every_Cone_Equalizes.

      Program Instance Lim_Cone_is_Limit : Limit D Lim_Cone :=
        {
          Lim_term := {| t_morph := Cone_Morph_to_Lim_Cone |}
        }.

      Next Obligation. (* t_morph_unique *)
      Proof.
        apply Cone_Morph_eq_simplify; destruct f as [hf hfc]; destruct g as [hg hgc]; simpl.
        apply (@mono_morphism_monomorphism _ _ _ _ _ (Equalizer_Monic Projs D_imgs)); simpl.
        unfold Lim_Cone in *; simpl in *.
        eapply GP_Prod_morph_unique; intros a; rewrite <- assoc; eauto.
      Qed.

    End Limits_Exist.
  End Gen_Prod_Eq_Limits.

  Section Restricted_Limits.
    Context (P : Card_Restriction) {CHRP : Has_Restricted_General_Products C P} {HE : Has_Equalizers C}.

    Program Instance Restr_Gen_Prod_Eq_Restr_Limits : Has_Restricted_Limits C P :=
      {
        Restricted_Limit_of := λ _ _ _ D PO PH, @Lim_Cone _ _ _ (HRGP_HGP _ PO) (HRGP_HGP _ PH) _ D;
        Restricted_Limit_of_Limit := λ _ _ _ D PO PH, @Lim_Cone_is_Limit _ _ _ (HRGP_HGP _ PO) (HRGP_HGP _ PH) _ D
      }.

  End Restricted_Limits.

    Section Complete.
    Context {CHAP : Has_All_General_Products C} {HE : Has_Equalizers C}.

    Program Instance Gen_Prod_Eq_Complete : Complete C :=
      {
        Limit_of := λ _ _ _ D, @Lim_Cone _ _ _ (HAGP_HGP _) (HAGP_HGP _) _ D;
        Limit_of_Limit := λ _ _ _ D, @Lim_Cone_is_Limit _ _ _ (HAGP_HGP _) (HAGP_HGP _) _ D
      }.

  End Complete.

End Gen_Prod_Eq_Complete.

