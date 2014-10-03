Require Import Category.Core.
Require Import Ext_Cons.Core.
Require Import Functor.Core.
Require Import Basic_Cons.Product.

Class Exponential `(C : Category Obj Hom) (HP : Has_Products C) (c d e : Obj) : Type :=
{
  eval : Hom (e × c) d;

  Exp_morph_ex : ∀ (z : Obj), Hom (z × c) d → Hom z e;

  Exp_morph_com : ∀ (z : Obj) (f : Hom (z × c) d), f = eval ∘ ≪ (Exp_morph_ex z f), @id _ _ _ c ≫;

  Exp_morph_unique : ∀ (z : Obj) (f : Hom (z × c) d) (u u' : Hom z e), f = eval ∘ ≪ u, @id _ _ _ c ≫ → f = eval ∘ ≪ u', @id _ _ _ c ≫ → u = u'
}.

Theorem Exponential_iso `(C : Category Obj Hom) (HP : Has_Products C) (c d e e' : Obj) :
  Exponential _ _ c d e -> Exponential _ _ c d e' -> e ≡ e'.
Proof.
  intros [ev1 mex1 mc1 mu1] [ev2 mex2 mc2 mu2].
  exists (mex2 e ev1); exists (mex1 e' ev2).
  {
    apply mu1 with (f := ev1); auto.
    match goal with
        [|- _ = _ ∘ ?U (?A ∘ ?B, ?C)] =>
        let H := fresh "H" in
      cut (U (A ∘ B, C) = U (A ∘ B, C ∘ C)); [intros H; rewrite H|simpl_ids; trivial]
    end
    .
    match goal with
        [|- _ = _ ∘ ?U _a _ _ (?A ∘ ?B, ?D ∘ ?D)] =>
        let H := fresh "H" in
        cut (U _a (_,_) (_,_) (A ∘ B, D ∘ D) = (U _a (_, _) (_, _) (A, D)) ∘ (U _a (_,_) (_,_) (B, D)));
          [intros H; rewrite H|rewrite <- F_compose; reflexivity]
    end
    .
    match goal with
        [|- _ = ?A ∘ ?B ∘ ?D] =>
        reveal_comp A B; replace (A ∘ B) with ev2; auto
    end
    .
  }
  {
    apply mu2 with (f := ev2); auto.
    match goal with
        [|- _ = _ ∘ ?U (?A ∘ ?B, ?C)] =>
        let H := fresh "H" in
        cut (U (A ∘ B, C) = U (A ∘ B, C ∘ C)); [intros H; rewrite H|simpl_ids; trivial]
    end
    .
    match goal with
        [|- _ = _ ∘ ?U _a _ _ (?A ∘ ?B, ?D ∘ ?D)] =>
        let H := fresh "H" in
        cut (U _a (_,_) (_,_) (A ∘ B, D ∘ D) = (U _a (_, _) (_, _) (A, D)) ∘ (U _a (_, _) (_,_) (B, D))) ; [intros H; rewrite H|rewrite <- F_compose; reflexivity]
    end
    .
    match goal with
        [|- _ = ?A ∘ ?B ∘ ?D] =>
        reveal_comp A B; replace (A ∘ B) with ev1; auto
    end
    .
  }
Qed.

Definition Arrow_Exponential `{C : Category Obj Hom}
           {a b c d x y : Obj}
           {hp : Has_Products C}
           (Eabx : Exponential C hp a b x)
           (Ecdy : Exponential C hp c d y)
           (f : Hom c a) (g : Hom b d) 
: Hom x y :=
  @Exp_morph_ex _ _ C _ _ _ _ Ecdy x (g ∘ (@eval _ _ _ _ _ _ _ Eabx) ∘ ≪ @id _ _ _ x, f ≫)
.

Program Instance Exponential_Functor `{C : Category Obj Hom}
        {hp : Has_Products C}
        (exp : Obj -> Obj -> Obj)
        (exp_exp : forall a b, Exponential C hp a b (exp a b))
: Functor (Prod_Cat (C ^op) C) C :=
{
  FO := fun x => exp (fst x) (snd x); 
  FA := fun a b f => Arrow_Exponential (exp_exp _ _) (exp_exp _ _) (fst f) (snd f)
}.

Next Obligation. (* F_id *)
Proof.
  simpl.
  match goal with
      [|- Arrow_Exponential ?A ?A _ _ = _] =>
      destruct A as [ev mex mc mu]
  end
  .
  eapply mu.
  unfold Arrow_Exponential, Exp_morph_ex.
  match goal with
      [|- _ = _ ∘ ≪ mex _ ?X, _ ≫] =>
      rewrite <- (mc _ X); reflexivity
  end.
  match goal with
      [|- ?A ∘ ?B ∘ ?C = _] =>
      reveal_comp A B; simpl_ids; trivial
  end
  .
Qed.

Next Obligation. (* F_compose *)
Proof.
  simpl in *.
  repeat match goal with
      | [|- context[(exp_exp ?A ?B)] ] =>
        let EV := fresh "ev" in
        let MEX := fresh "mex" in
        let MC := fresh "mc" in
        let MU := fresh "mu" in
        destruct (exp_exp A B) as [EV MEX MC MU]
  end
  .
  unfold Arrow_Exponential, Exp_morph_ex, eval.
  eapply mu0.
  rewrite <- mc0; reflexivity.
  match goal with
      [|- _ = _ ∘ ≪ ?B ∘ ?D, ?A ≫] =>
      let H := fresh "H" in
      cut (≪ B ∘ D, A ≫ = ≪ B, A ≫ ∘ ≪ D, A ≫); [intros H; rewrite H; clear H| rewrite <- F_compose; simpl; simpl_ids; reflexivity ]
  end
  .
  match goal with
      [|- _ = ?A ∘ ?B ∘ ?D] =>
      reveal_comp A B;
        match B with
            (≪ mex0 _ ?E, _ ≫) =>
            let H := fresh "H" in
            assert (H := mc0 _ E); rewrite <- H; clear H
        end
  end
  .
  repeat rewrite assoc.
  match goal with
      [|- _ = _ ∘ ?A ∘ ?B ∘ ?D] =>
        match B with
            (≪ id, ?E ≫) =>
            match type of E with
                Hom ?G ?H =>
                match D with
                    (≪ ?F, id ≫) =>
                    match type of F with
                        Hom ?I ?J =>
                        replace (B ∘ D) with (≪ F, @id _ _ _ H ≫ ∘ ≪ @id _ _ _ I, E ≫)
                    end
                end
            end
        end
  end
  .
  {
    match goal with
        [|- _ = _ ∘ ?A ∘ ?B ∘ ?D] =>
        reveal_comp A B;
          match B with
              (≪ mex1 _ ?E, id ≫) =>
              let H := fresh "H" in
              assert (H := mc1 _ E); rewrite <- H; clear H
          end
    end
    .
    repeat rewrite assoc.
    rewrite <- F_compose; simpl; simpl_ids; trivial.
  }
  {
    repeat rewrite <- F_compose; simpl; simpl_ids; reflexivity.
  }          
Qed.

(* Exponential_Functor defined *)


Class Has_Exponentials `(C : Category Obj Hom) {hp : Has_Products C} : Type :=
{
  HE_exp : Obj → Obj → Obj;

  HE_exp_exp : ∀ a b, Exponential C hp a b (HE_exp a b);

  HE_exp_ftor := Exponential_Functor HE_exp HE_exp_exp where "x ↑ y" := (HE_exp_ftor _o (y, x)) and "f ↑↑ g" := (HE_exp_ftor _a (_, _) (_, _) (g, f));

  curry : forall {a b c : Obj}, Hom (a × b) c → Hom a (c ↑ b)  :=
    fun {a b c : Obj} (f : Hom (a × b) c) =>
      @Exp_morph_ex _ _ _ _ _ _ _ (HE_exp_exp b c) _ f
  ;

  uncurry : forall {a b c : Obj}, Hom a (c ↑ b) -> Hom (a × b) c :=
    fun {a b c : Obj} (f : Hom a (c ↑ b)) =>
      (@eval _ _ _ _ _ _ _ (HE_exp_exp b c)) ∘ ≪ f , @id _ _ _ b ≫
}.

Notation "x ↑ y" := (HE_exp_ftor _o (y, x)).
Notation "f ↑↑ g" := (HE_exp_ftor _a (_, _) (_, _) (g, f)).

Existing Instance HE_exp_exp.

Section Curry_UnCurry.

  Context  `{C : Category Obj} {HP : Has_Products C} {HE : Has_Exponentials C} {a b c : Obj}.

  Theorem curry_uncurry (f : Hom a (c ↑ b)) : curry (uncurry f) = f.
  Proof.
    unfold curry, uncurry.
    eapply Exp_morph_unique.
    rewrite <- Exp_morph_com.
    reflexivity.
    trivial.
  Qed.

  Theorem uncurry_curry (f : Hom (a × b) c) : uncurry (curry f) = f.
  Proof.
    unfold curry, uncurry.
    rewrite <- Exp_morph_com.
    reflexivity.
  Qed.

End Curry_UnCurry.


