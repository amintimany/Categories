Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Cat.Cat_Product Cat.Cat_Exponential.

Local Obligation Tactic := idtac.

Section Exp_Cat_morph_ex_compose.
  Context {C C' C'' : Category} (F : Functor (Prod_Cat C'' C)  C') {B : Category} (G : Functor B C'').

  Theorem Exp_Cat_morph_ex_compose : Exp_Cat_morph_ex (Functor_compose (Prod_Functor G (Functor_id C)) F) = Functor_compose G (Exp_Cat_morph_ex F).
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    {
      extensionality x; extensionality y; extensionality h.
      match goal with
        [|- match _ in _ = V return _ with eq_refl => ?A end h = ?B] =>
        transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A h end)
      end.
      destruct W; trivial.
      apply NatTrans_eq_simplify.
      apply JMeq_eq.
      destruct W; trivial.
    }
    {
      extensionality x.
      match goal with
        [|- ?A = ?B] =>
        set(W := eq_refl : A _o = B _o); apply (Functor_eq_simplify _ _ W)
      end.
      extensionality z; extensionality y; extensionality h.
      cbn.
      rewrite F_id; trivial.
    }
  Qed.

End Exp_Cat_morph_ex_compose.

Section Exp_Cat_morph_ex_NT.
  Context {C C' C'' : Category} {F F' : Functor (Prod_Cat C'' C)  C'} (N : NatTrans F F').
  Program Instance Exp_Cat_morph_ex_NT : NatTrans (Exp_Cat_morph_ex F) (Exp_Cat_morph_ex F') :=
    {
      Trans := fun d =>
                 {|
                   Trans := fun c => Trans N (d, c);
                   Trans_com := fun c c' h => @Trans_com _ _ _ _ N (d, c) (d ,c') (id,  h);
                   Trans_com_sym := fun c c' h => @Trans_com_sym _ _ _ _ N (d, c) (d ,c') (id,  h)
                 |}
    }.

  Next Obligation.
  Proof.  
    intros c c' h; cbn.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply Trans_com.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Exp_Cat_morph_ex_NT_obligation_1.
  Qed.

End Exp_Cat_morph_ex_NT.

Section Exp_Cat_morph_ex_Iso.
  Context {C C' C'' : Category} {F F' : Functor (Prod_Cat C'' C)  C'} (N : F ≡≡ F' ::> Func_Cat _ _).

  Program Instance Exp_Cat_morph_ex_Iso : Exp_Cat_morph_ex F ≡≡ Exp_Cat_morph_ex F' ::> Func_Cat _ _ :=
    {
      iso_morphism := Exp_Cat_morph_ex_NT (iso_morphism N);
      inverse_morphism := Exp_Cat_morph_ex_NT (inverse_morphism N)
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply NatTrans_eq_simplify; extensionality y; cbn.
    change (Trans N ⁻¹ (x, y) ∘ Trans (iso_morphism N) (x, y)) with (Trans (N⁻¹ ∘ N) (x, y)).
    rewrite left_inverse; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    apply NatTrans_eq_simplify; extensionality y; cbn.
    change (Trans (iso_morphism N) (x, y) ∘ Trans N⁻¹ (x, y)) with (Trans (N ∘ N⁻¹) (x, y)).
    rewrite right_inverse; trivial.
  Qed.

End Exp_Cat_morph_ex_Iso.

Section Exp_Cat_morph_ex_inverse_NT.
  Context {C C' C'' : Category} {F F' : Functor (Prod_Cat C'' C)  C'} (N : NatTrans (Exp_Cat_morph_ex F) (Exp_Cat_morph_ex F')).

  Program Instance Exp_Cat_morph_ex_inverse_NT : NatTrans  F F' :=
    {
      Trans := fun d => Trans (Trans N (fst d)) (snd d)
    }.
    
  Next Obligation.
  Proof.  
    intros [d1 d2] [d1' d2'] [h1 h2]; cbn in *.
    replace (F _a (_, _) (_, _) (h1, h2)) with ((F _a (_, _) (_, _) (id d1', h2)) ∘ (F _a (_, _) (_, _) (h1, id d2))) by auto.
    rewrite assoc_sym.   
    set (W := (Trans_com (Trans N d1') h2)); cbn in W; rewrite W; clear W.
    rewrite assoc.
    set (W := f_equal (fun w : NatTrans (Fix_Bi_Func_1 d1 F) (Fix_Bi_Func_1 d1' F') => Trans w d2) (Trans_com N h1)); cbn in W; rewrite W; clear W.
    rewrite assoc_sym.
    rewrite <- F_compose.
    cbn; auto.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Exp_Cat_morph_ex_inverse_NT_obligation_1.
  Qed.

End Exp_Cat_morph_ex_inverse_NT.

Section Exp_Cat_morph_ex_inverse_Iso.
  Context {C C' C'' : Category} {F F' : Functor (Prod_Cat C'' C)  C'} (N : Exp_Cat_morph_ex F ≡≡ Exp_Cat_morph_ex F' ::> Func_Cat _ _).

  Program Instance Exp_Cat_morph_ex_inverse_Iso :  F ≡≡ F' ::> Func_Cat _ _ :=
    {
      iso_morphism := Exp_Cat_morph_ex_inverse_NT (iso_morphism N);
      inverse_morphism := Exp_Cat_morph_ex_inverse_NT (inverse_morphism N)
    }.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    match goal with
      [|- ?U = _] =>
      match U with
        Trans (Trans ?A ?X) ?Y ∘ Trans (Trans ?B ?X) ?Y =>
        change U with (Trans (Trans (NatTrans_compose B A) X) Y)
      end
    end.
    set (W := left_inverse N); cbn in W.
    rewrite W.
    trivial.
  Qed.
  
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality x; cbn.
    match goal with
      [|- ?U = _] =>
      match U with
        Trans (Trans ?A ?X) ?Y ∘ Trans (Trans ?B ?X) ?Y =>
        change U with (Trans (Trans (NatTrans_compose B A) X) Y)
      end
    end.
    set (W := right_inverse N); cbn in W.
    rewrite W.
    trivial.
  Qed.

End Exp_Cat_morph_ex_inverse_Iso.
