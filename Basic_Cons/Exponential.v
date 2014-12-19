Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Basic_Cons.Product.

Set Primitive Projections.

Set Universe Polymorphism.


Class Exponential {C : Category} {HP : Has_Products C} (c d : Obj) : Type :=
{
  exponential : C;

  eval : Hom (Prod_Func _o (exponential, c)) d;

  Exp_morph_ex : ∀ (z : C), Hom (Prod_Func _o (z, c)) d → Hom z exponential;

  Exp_morph_com : ∀ (z : C) (f : Hom (Prod_Func _o (z, c)) d), f = eval ∘ (Prod_Func _a (_, _) (_, _) (Exp_morph_ex z f, @id _ c));

  Exp_morph_unique : ∀ (z : C) (f : Hom (Prod_Func _o (z, c)) d) (u u' : Hom z exponential), f = eval ∘ (Prod_Func _a (_, _) (_, _) (u, @id _ c)) → f = eval ∘ (Prod_Func _a (_, _) (_, _) (u', @id _ c)) → u = u'
}.

Coercion exponential : Exponential >-> Obj.

Theorem Exponential_iso {C : Category} {HP : Has_Products C} (c d : C) (E E' : Exponential c d) : E ≡ E'.
Proof.
  eapply (@Build_Isomorphism _ _ _ (Exp_morph_ex E eval) (Exp_morph_ex E' eval)); eapply Exp_morph_unique; eauto;
  simpl_ids;
  match goal with
      [|- _ ∘ ?M = _] =>
      match M with
          ?U _a _ _ (?A ∘ ?B, ?C) => cutrewrite (M = (U _a (_, _) (_, _) (A, C)) ∘ (U _a (_, _) (_, _) (B, C))); [|simpl_ids; rewrite <- F_compose; simpl; simpl_ids; trivial]
      end
  end;
  rewrite <- assoc;
  repeat rewrite <- Exp_morph_com; auto.
Qed.

Class Has_Exponentials (C : Category) {HP : Has_Products C} := has_exponentials : ∀ a b, Exponential a b.

Section Curry_UnCurry.
  Context (C : Category) {HP : Has_Products C} {HE : Has_Exponentials C}.

  Definition curry : forall {a b c : C}, @Hom C (Prod_Func _o (a, b)) c → @Hom C a (HE b c) :=
    fun {a b c : C} (f : @Hom C (Prod_Func _o (a, b)) c) =>
      @Exp_morph_ex _ _ _ _ (HE b c) _ f.
      
  Definition uncurry : forall {a b c : C}, @Hom C a (HE b c) → @Hom C (Prod_Func _o (a, b)) c :=
    fun {a b c : C} (f : Hom a (HE b c)) =>
      (@eval _ _ _ _ (HE b c)) ∘ (Prod_Func _a (_, _) (_, _) (f, @id C b)).

  Context {a b c : C}.

  Theorem curry_uncurry (f : Hom a (HE b c)) : curry (uncurry f) = f.
  Proof.
    unfold curry, uncurry.
    eapply Exp_morph_unique; trivial.
    rewrite <- Exp_morph_com; trivial.
  Qed.

  Theorem uncurry_curry (f : Hom (Prod_Func _o (a, b)) c) : uncurry (curry f) = f.
  Proof.
    unfold curry, uncurry.
    rewrite <- Exp_morph_com; trivial.
  Qed.

End Curry_UnCurry.
