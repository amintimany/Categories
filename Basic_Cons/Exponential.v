Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Basic_Cons.Product.

Class Exponential {C : Category} {HP : Has_Products C} (c d : Obj) : Type :=
{
  exponential : C;

  eval : Hom ((Prod_Func C) _o (exponential, c)) d;

  Exp_morph_ex : ∀ (z : C), Hom ((Prod_Func C) _o (z, c)) d → Hom z exponential;

  Exp_morph_com : ∀ (z : C) (f : Hom ((Prod_Func C) _o (z, c)) d), f = eval ∘ ((Prod_Func C) _a (_, _) (_, _) (Exp_morph_ex z f, id c));

  Exp_morph_unique : ∀ (z : C) (f : Hom ((Prod_Func C) _o (z, c)) d) (u u' : Hom z exponential), f = eval ∘ ((Prod_Func C) _a (_, _) (_, _) (u, id c)) → f = eval ∘ ((Prod_Func C) _a (_, _) (_, _) (u', id c)) → u = u'
}.

Coercion exponential : Exponential >-> Obj.

Arguments Exponential _ {_} _ _, {_ _} _ _.

Arguments exponential {_ _ _ _} _, {_ _} _ _ {_}.
Arguments eval {_ _ _ _} _, {_ _} _ _ {_}.
Arguments Exp_morph_ex {_ _ _ _} _ _ _, {_ _} _ _ {_} _ _.
Arguments Exp_morph_com {_ _ _ _} _ _ _, {_ _} _ _ {_} _ _.
Arguments Exp_morph_unique {_ _ _ _} _ _ _ _ _ _ _, {_ _} _ _ {_} _ _ _ _ _ _.

Theorem Exponential_iso {C : Category} {HP : Has_Products C} (c d : C) (E E' : Exponential c d) : E ≡ E'.
Proof.
  eapply (Build_Isomorphism _ _ _ (Exp_morph_ex E' _ (eval E)) (Exp_morph_ex E _ (eval E'))); eapply Exp_morph_unique; eauto;
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

Definition Has_Exponentials (C : Category) {HP : Has_Products C} := ∀ a b, Exponential a b.

Existing Class Has_Exponentials.

Section Curry_UnCurry.
  Context (C : Category) {HP : Has_Products C} {HE : Has_Exponentials C}.

  Definition curry : forall {a b c : C}, Hom C ((Prod_Func C) _o (a, b)) c → Hom C a (HE b c) :=
    fun {a b c : C} (f : Hom C ((Prod_Func C) _o (a, b)) c) =>
      Exp_morph_ex (HE b c) _ f.
      
  Definition uncurry : forall {a b c : C}, Hom C a (HE b c) → Hom C ((Prod_Func C) _o (a, b)) c :=
    fun {a b c : C} (f : Hom a (HE b c)) =>
      (eval (HE b c)) ∘ ((Prod_Func C) _a (_, _) (_, _) (f, id C b)).

  Section inversion.
    Context {a b c : C}.

    Theorem curry_uncurry (f : Hom a (HE b c)) : curry (uncurry f) = f.
    Proof.
      unfold curry, uncurry.
      eapply Exp_morph_unique; trivial.
      rewrite <- Exp_morph_com; trivial.
    Qed.

    Theorem uncurry_curry (f : Hom ((Prod_Func C) _o (a, b)) c) : uncurry (curry f) = f.
    Proof.
      unfold curry, uncurry.
      rewrite <- Exp_morph_com; trivial.
    Qed.

  End inversion.

  Section injectivity.
    Context {a b c : C}.

    Theorem curry_injective (f g : Hom ((Prod_Func C) _o (a, b)) c) : curry f = curry g → f = g.
    Proof.
      intros H.
      rewrite <- (uncurry_curry f); rewrite <- (uncurry_curry g).
      rewrite H; trivial.
    Qed.

    Theorem uncurry_injective (f g : Hom a (HE b c)) : uncurry f = uncurry g → f = g.
    Proof.
      intros H.
      rewrite <- (curry_uncurry f); rewrite <- (curry_uncurry g).
      rewrite H; trivial.
    Qed.

  End injectivity.

  Section curry_compose.
    Context {a b c : C}.

    Lemma curry_compose (f : Hom ((Prod_Func C) _o (a, b)) c) {z : C} (g : Hom z a) : (curry f) ∘ g = curry (f ∘ (Prod_morph_ex _ _ (g ∘ Pi_1) Pi_2)).
    Proof.
      unfold curry.
      eapply Exp_morph_unique; eauto.
      rewrite <- Exp_morph_com.
      match goal with
          [|- (_ ∘ (_ _a) _ _ ?M) ∘ _ = _] =>
          match M with
              (?N ∘ ?x, id ?y) =>
              replace M with (compose (Prod_Cat _ _) (_, _) (_, _) (_, _) (x, id y) (N,id y)) by (cbn; auto)
          end
      end.
      rewrite F_compose.
      cbn; simpl_ids.
      rewrite assoc_sym.
      match goal with
          [|- ?A ∘ ?B = ?C ∘ ?B] => cutrewrite (A = C); trivial
      end.
      transitivity (uncurry (curry f)); [unfold curry, uncurry; cbn; auto|apply uncurry_curry].
    Qed.      

  End curry_compose.

End Curry_UnCurry.
