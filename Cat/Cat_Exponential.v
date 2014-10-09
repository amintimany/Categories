Require Import Cat.Cat_Product.

Require Import Coq.Logic.EqdepFacts.

Require Import Category.Core.
Require Import Functor.Core.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans.

Local Obligation Tactic := idtac.

Program Instance Exp_Cat_eval `(C : Category Obj Hom) `(C' : Category Obj' Hom') : Functor (Prod_Cat (Func_Cat C C') C) C' :=
{
  FO := fun x => (fst x) _o (snd x);
  FA := fun A B f => ((fst B) _a _ _ (snd f)) ∘ (@Trans _ _ _ _ _ _ _ _ (fst f) _)
}.

Next Obligation. (* F_id *)
Proof.
  program_simpl.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros Obj Hom C Obj' Hom' C' [D1 x1] [D2 x2] [D3 x3] [f1 f2] [g1 g2].
  simpl in *.
  match goal with
      [|- ?A ∘ ?B ∘ ?D = ?E ∘ ?F ∘ ?G] =>
      reveal_comp A B; reveal_comp E F; f_equal
  end
  .
  match goal with
      [|- ?A ∘ ?B = _] =>
        match A with
            ?F _a _ _ ?X =>
            match goal with
                [H : NatTrans _ F |- _] =>
                let H' := fresh "H" in
                assert (H' := @Trans_com _ _ _ _ _ _ _ _ H _ _ X); symmetry in H'; rewrite H'
            end
        end
  end
  .
  rewrite F_compose.
  match goal with
      [|- ?A ∘ ?B ∘ ?D = _] =>
      reveal_comp A B; f_equal
  end
  .
  apply Trans_com.
Qed.

(* Exp_Cat_Eval defined *)

Local Obligation Tactic := program_simpl; auto.

Program Instance Exp_Cat_morph_ex_O `{C : Category Obj Hom} `{C' : Category Obj' Hom'} `{C'' : Category Obj'' Hom''} (F : Functor (Prod_Cat C'' C)  C') (a : Obj'') : Functor C C' :=
{
  FO := fun x => F _o (a, x);
  FA := fun _ _ f => F _a _ _ (@id _ _ _ a, f)
}.

(* Exp_Cat_morph_ex_O defined *)

Program Instance Exp_Cat_morph_ex_A `{C : Category Obj Hom} `{C' : Category Obj' Hom'} `{C'' : Category Obj'' Hom''} (F : Functor (Prod_Cat C'' C)  C') (a b : Obj'') (h : Hom'' a b) : NatTrans (Exp_Cat_morph_ex_O F a) (Exp_Cat_morph_ex_O F b) :=
{
  Trans := fun c => F _a _ _ (h, @id _ _ _ c)
}.

(* Exp_Cat_morph_ex_A defined *)

Program Instance Exp_Cat_morph_ex `{C : Category Obj Hom} `{C' : Category Obj' Hom'} `{C'' : Category Obj'' Hom''} (F : Functor (Prod_Cat C'' C)  C') : Functor C'' (Func_Cat C C') :=
{
  FO := Exp_Cat_morph_ex_O F;
  FA := Exp_Cat_morph_ex_A F
}.

Next Obligation. (* F_id *)
Proof.
  apply NatTrans_eq_simplify; trivial.
Qed.

Next Obligation. (* F_compose *)
Proof.
  apply NatTrans_eq_simplify; simpl.
  extensionality x.
  rewrite <- F_compose; simpl; simpl_ids; trivial.
Qed.

(* Exp_Cat_morph_ex *)

Local Obligation Tactic := idtac.

Program Instance Cat_Exponentials (C : CAT) (C' : CAT) : Exponential Cat Cat_Has_Products C C' (mkCAT _ _ (Func_Cat (THE_CAT C) (THE_CAT C'))) :=
{
  eval := Exp_Cat_eval (THE_CAT C) (THE_CAT C');
  
  Exp_morph_ex := fun C'' F => @Exp_Cat_morph_ex _ _ (THE_CAT C) _ _ (THE_CAT C') _ _ (THE_CAT C'') F
}.

Next Obligation. (* Exp_morph_com *)
Proof.
  intros C C' z f.
  Functor_extensionality a b F.
  destruct a; trivial.
  simpl.
  rewrite <- F_compose.
  simpl; simpl_ids.
  destruct a; destruct b; destruct F; simpl; trivial.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
  intros C C' z f u u' H1 H2.
  program_simpl.
  destruct C as [Obj Hom C]; destruct C' as [Obj' Hom' C'].
  cut (u _o = u' _o); [intros HO|].
  apply Functor_eq_simplify.
  {
    trivial.
  }
  {
    FA_extensionality a b F.
    destruct z as [Objz Homz z]; destruct u as [uO uA uid ucomp]; destruct u' as [uO' uA' uid' ucomp']; simpl in *.
    set (HN := (eq_ind_r (fun f : Objz -> (Functor C C') => NatTrans (f a) (f b) = NatTrans (uO' a) (uO' b)) eq_refl HO)).
    set (uAabf' := (
                    match HN in (_ = Z) return Z with
                      |eq_refl =>
                       uA a b F
                    end
        )).
    apply (@JMeq_trans _ _ _ _ uAabf'); [destruct HN; trivial|
               match goal with
                   [|- ?A ~= ?B] =>
                   let H' := fresh "H" in
                   cut (A = B); [intros H'; rewrite H'; trivial|]
               end
              ].
    apply NatTrans_eq_simplify.
    extensionality c.
    unfold Trans.
    match goal with
        [|- ?A = ?B] =>
        let H' := fresh "H" in
        cut (A ~= B); [intros H'; rewrite H'; trivial|]
    end.
    match goal with
        [H' : ?A = ?B , H : existT _ ?A _ = existT _ ?B _ |- _] =>
        apply eq_sigT_eq_dep in H; apply eq_dep_JMeq in H;
        let H'' := fresh "H" in
        assert (H'' := @FA_equal_f _ _ _ _ _ _ _ _ H' H (_, _) (_, _) (F, @id _ _ _ c)); simpl in H'';
        repeat rewrite F_id in H'';
        repeat rewrite id_unit_left in H'';
        unfold Trans in H'';
        rewrite <- H''
    end.
    destruct HO; simpl in *; reflexivity.
  }
  {
    extensionality x.
    Functor_extensionality a b F.
    match goal with
        [H' : ?A = ?B , H : existT _ ?A _ = existT _ ?B _ |- _] =>
        apply (fun p => equal_f p (x, a)) in H'; trivial
    end.
    match goal with
        [H' : ?A = ?B , H : existT _ ?A _ = existT _ ?B _ |- _] =>
        apply eq_sigT_eq_dep in H; apply eq_dep_JMeq in H;
        let H'' := fresh "H" in
        assert (H'' := @FA_equal_f _ _ _ _ _ _ _ _ H' H (_, _) (_, _) (@id _ _ (THE_CAT z) x, F));
          unfold Trans in H'';
          simpl in H'';
          repeat (repeat rewrite F_id in H'';
          simpl in H'');
          repeat rewrite id_unit_right in H'';
          trivial
    end.
  }
Qed.

(* Cat_Exponentials defined *)

Instance Cat_Has_Exponentials : Has_Exponentials Cat :=
{
  HE_exp := fun C C' => (mkCAT _ _ (Func_Cat (THE_CAT C) (THE_CAT C')));
  HE_exp_exp := Cat_Exponentials
}.



