(**
     This file contians facts about the category of categories (Cat) defined in Functor module.
*)

Require Import Coq.Logic.EqdepFacts.

Require Import Category.Core.
Require Import Functor.Core.
Require Import Cat.Cat.
Require Import Ext_Cons.Core.
Require Import Basic_Cons.Core.
Require Import NatTrans.NatTrans.
Require Export Essentials.Types.

(* Empty_Cat the empty category -- the initial object of Cat *)

Program Instance Empty_Cat : Category Empty (λ x y, Empty) :=
{
  compose := fun a b c f g => Empty_rect _ f;

  id := fun x => Empty_rect _ x
}.

(* Empty_Cat defined *)

Program Instance Functor_From_Empty_Cat `(C' : Category Obj) : Functor Empty_Cat C' :=
{
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => Empty_rect _ f
}.

(* Functor_From_Empty_Cat defined *)

Program Instance Cat_Init : Initial Cat (mkCAT _ _ Empty_Cat) :=
{
  i_morph := fun x => Functor_From_Empty_Cat (THE_CAT x)
}.

Next Obligation. (* i_morph_unique *)
Proof.
  Functor_extensionality a b F; contradiction.
Qed.

(* Cat_init defined *)

Program Instance Cat_Has_Initial : Has_Initial Cat.


(* Singleton_Cat the category with a single object and its identity -- the terminal object of Cat *)

Program Instance Singleton_Cat : Category Singleton_Type (λ x y, Singleton_Type) :=
{
  compose := fun a b c f g => ST;

  id := fun x => ST
}.

Next Obligation. (* id_unit_left *)
Proof.
  destruct h; trivial.
Qed.

Next Obligation. (* id_unit_right *)
Proof.
  destruct h; trivial.
Qed.

(* Singleton_Cat defined -- the rest of the obligations are taken care of by Program system *)

Program Instance Functor_To_Singleton_Cat `(C' : Category Obj) : Functor C' Singleton_Cat :=
{
  FO := fun x => ST;
  FA := fun a b f => ST
}.

(* Functor_To_Singleton_Cat defined *)

Program Instance Cat_Term : Terminal Cat (mkCAT _ _ Singleton_Cat) :=
{
  t_morph := fun x => Functor_To_Singleton_Cat (THE_CAT x)
}.

Next Obligation. (* t_morph_unique *)
Proof.
  Functor_extensionality a b F.
  match goal with
      [|- ?A = ?B] =>
      destruct A; destruct B; trivial
  end.
  match goal with
      [|- ?A ~= ?B] =>
      destruct A; destruct B; trivial
  end.
Qed.

(* Cat_term defined *)

Program Instance Cat_Has_Terminal : Has_Terminal Cat.


Program Instance Prod_Cat_proj1 `(C : Category Obj) `(C' : Category Obj') : Functor (Prod_Cat C C') C :=
{
  FO := fun x => fst x;
  FA := fun _ _ f => fst f
}.

(* Prod_Cat_Proj1 defined *)

Program Instance Prod_Cat_proj2 `(C : Category Obj) `(C' : Category Obj') : Functor (Prod_Cat C C') C' :=
{
  FO := fun x => snd x;
  FA := fun _ _ f => snd f
}.

(* Prod_Cat_Proj2 defined *)


Program Instance Prod_Cat_morph_ex `(C : Category Obj) `(C' : Category Obj') `(C'' : Category Obj'') (F : Functor C''  C) (G : Functor C'' C') : Functor C'' (Prod_Cat C C') :=
{
  FO := fun x => (F _o x, G _o x);
  FA := fun _ _ f => (F _a _ _ f, G _a _ _ f)
}.

(* Prod_Cat_morph_ex defined *)


Program Instance Cat_Products (C : CAT) (C' : CAT) : Product Cat C C' (mkCAT _ _ (Prod_Cat (THE_CAT C) (THE_CAT C'))) :=
{
  Pi_1 := Prod_Cat_proj1 (THE_CAT C) (THE_CAT C');
  Pi_2 := Prod_Cat_proj2 (THE_CAT C)(THE_CAT C');

  Prod_morph_ex := fun P => fun F G => Prod_Cat_morph_ex (THE_CAT C) (THE_CAT C') (THE_CAT P) F G
}.

Next Obligation. (* Prod_morph_com1 *)
Proof.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Next Obligation. (* Prod_morph_com2 *)
Proof.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Next Obligation. (* Prod_morph_unique *)
Proof.
  cut (f _o = g _o); [intros HO|].
  {
    apply Functor_eq_simplify.
    {
      trivial.
    }
    {
      FA_extensionality a b F.
      repeat match goal with
                 [H : existT _ _ _ = existT _ _ _ |- _] =>
                 apply eq_sigT_eq_dep in H; apply eq_dep_JMeq in H
             end.
      
      match goal with
      [|- ?A ~= ?B] =>
      cut ((fst A, snd A) ~= (fst B, snd B)); [destruct A; destruct B; simpl; trivial|]
      end.
      eapply FA_equal_f in H3; trivial.
      eapply FA_equal_f in H4; trivial.
      match goal with
          [|- (?A, ?B) ~= (?C, ?D)] =>
          cut (A ~= C); [intros HU; rewrite HU; cut (B ~= D); [intros HU'; rewrite HU'; trivial| symmetry; exact H4]| symmetry; exact H3]
      end.
    }
  }      
  {
    extensionality x.
    apply (fun p => equal_f p x) in H0; apply (fun p => equal_f p x) in H1.
    simpl in H0, H1; simpl.
    match goal with
        [|- ?A = ?B] =>
        destruct A; destruct B; simpl in H0, H1; subst; trivial
    end.
  }
Qed.


(* Cat_Products defined *)

Program Instance Cat_Has_Products : Has_Products Cat :=
{
  HP_prod := fun C C' => (mkCAT _ _ (Prod_Cat (THE_CAT C) (THE_CAT C')));
  HP_prod_prod := Cat_Products
}.


Program Instance Exp_Cat_eval `(C : Category Obj) `(C' : Category Obj') : Functor (Prod_Cat (Func_Cat C C') C) C' :=
{
  FO := fun x => (fst x) _o (snd x);
  FA := fun A B f => ((fst B) _a _ _ (snd f)) ∘ (@Trans _ _ _ _ _ _ _ _ (fst f) _)
}.

Next Obligation. (* F_compose *)
Proof.
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

Program Instance Exp_Cat_morph_ex_O `{C : Category Obj} `{C' : Category Obj'} `{C'' : Category Obj''} (F : Functor (Prod_Cat C'' C)  C') (a : Obj'') : Functor C C' :=
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

Program Instance Exp_Cat_morph_ex `{C : Category Obj} `{C' : Category Obj'} `{C'' : Category Obj''} (F : Functor (Prod_Cat C'' C)  C') : Functor C'' (Func_Cat C C') :=
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

Program Instance Cat_Exponentials (C : CAT) (C' : CAT) : Exponential Cat Cat_Has_Products C C' (mkCAT _ _ (Func_Cat (THE_CAT C) (THE_CAT C'))) :=
{
  eval := Exp_Cat_eval (THE_CAT C) (THE_CAT C');
  
  Exp_morph_ex := fun C'' F => @Exp_Cat_morph_ex _ _ (THE_CAT C) _ _ (THE_CAT C') _ _ (THE_CAT C'') F
}.

Next Obligation. (* Exp_morph_com *)
Proof.
  Functor_extensionality a b F.
  destruct a; trivial.
  simpl.
  rewrite <- F_compose.
  simpl; simpl_ids.
  destruct a; destruct b; destruct F; simpl; trivial.
Qed.

Next Obligation. (* Exp_morph_unique *)
Proof.
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

    destruct HO.
    simpl in *.
    reflexivity.
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
          repeat rewrite id_unit_right in H''
    end.
    trivial.
  }
Qed.

(* Cat_Exponentials defined *)

Program Instance Cat_Has_Exponentials : Has_Exponentials Cat :=
{
  HE_exp := fun C C' => (mkCAT _ _ (Func_Cat (THE_CAT C) (THE_CAT C')));
  HE_exp_exp := Cat_Exponentials
}.


Program Instance Cat_CCC : CCC Cat.





