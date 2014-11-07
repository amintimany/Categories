Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Basic_Cons.Product.

Set Primitive Projections.

Set Universe Polymorphism.

Class Exponential (C : Category) (HP : Has_Products C) (c d e : Obj) : Type :=
{
  eval : Hom (Prod_of _o (e, c)) d;

  Exp_morph_ex : ∀ (z : Obj), Hom (Prod_of _o (z, c)) d → Hom z e;

  Exp_morph_com : ∀ (z : Obj) (f : Hom (Prod_of _o (z, c)) d), f = eval ∘ (Prod_of _a (_, _) (_, _) (Exp_morph_ex z f, @id _ c));

  Exp_morph_unique : ∀ (z : Obj) (f : Hom (Prod_of _o (z, c)) d) (u u' : Hom z e), f = eval ∘ (Prod_of _a (_, _) (_, _) (u, @id _ c)) → f = eval ∘ (Prod_of _a (_, _) (_, _) (u', @id _ c)) → u = u'
}.

Theorem Exponential_iso (C : Category) (HP : Has_Products C) (c d e e' : Obj) :
  Exponential _ _ c d e -> Exponential _ _ c d e' -> e ≡ e'.
Proof.
  intros H1 H2.
  exists (Exp_morph_ex e (@eval _ _ _ _ _ H1)).
  eexists (Exp_morph_ex e' (@eval _ _ _ _ _ H2)).
  {
    eapply Exp_morph_unique.
    match goal with
        [|- _ = _ ∘ ?U _a _ _ (?A ∘ ?B, ?C)] =>
        let H := fresh "H" in
        cutrewrite (U _a (_, _) (_, _) (A ∘ B, C) = (U _a (_, _) (_, _) (A, C)) ∘ (U _a (_, _) (_, _) (B, C))); [|simpl_ids; rewrite <- F_compose; simpl; simpl_ids; trivial]
    end.
    + rewrite <- assoc.
      repeat rewrite <- Exp_morph_com; reflexivity.
    + auto.
  }
  {
    eapply Exp_morph_unique.
    match goal with
        [|- _ = _ ∘ ?U _a _ _ (?A ∘ ?B, ?C)] =>
        let H := fresh "H" in
        cutrewrite (U _a (_, _) (_, _) (A ∘ B, C) = (U _a (_, _) (_, _) (A, C)) ∘ (U _a (_, _) (_, _) (B, C))); [|simpl_ids; rewrite <- F_compose; simpl; simpl_ids; trivial]
    end.
    + rewrite <- assoc.
      repeat rewrite <- Exp_morph_com; reflexivity.
    + auto.
  }
Qed.

Program Definition Arrow_Exponential {C : Category}
           {a b c d x y : Obj}
           {hp : Has_Products C}
           (Eabx : Exponential C hp a b x)
           (Ecdy : Exponential C hp c d y)
           (f : Hom c a) (g : Hom b d) 
: Hom x y :=
  @Exp_morph_ex C _ _ _ _ Ecdy x (g ∘ (@eval _ _ _ _ _ Eabx) ∘ (Prod_of _a (_, _) (_, _) (@id _ x, f)))
.

Program Instance Exponential_Functor {C : Category}
        {hp : Has_Products C}
        (exp : Obj -> Obj -> Obj)
        (exp_exp : forall a b, Exponential C hp a b (exp a b))
: Functor (Prod_Cat (C ^op) C) C :=
{
  FO := fun x => exp (fst x) (snd x); 
  FA := fun a b f => @Exp_morph_ex C _ _ _ _ (exp_exp _ _) _ ((snd f) ∘ (@eval _ _ _ _ _ (exp_exp _ _)) ∘ (Prod_of _a (_, _) (_, _) (@id _ (exp _ _), (fst f))))
}.

Next Obligation. (* F_id *)
Proof.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com.
  reflexivity.
  simpl; simpl_ids; reflexivity.
Qed.

Local Obligation Tactic := idtac.
Next Obligation. (* F_compose *)
Proof.
  intros.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com; reflexivity.
  match goal with
        [|- _ = _ ∘ ?U _a _ _ (?W, ?C)] =>
        match W with
            ?A ∘ ?B =>
            let H := fresh "H" in
            cutrewrite (U _a (_, _) (_, _) (W, C) = (U _a (_, _) (_, _) (A, C)) ∘ (U _a (_, _) (_, _) (B, C)))
        end
    end.
  {
    rewrite <- (@assoc _ _ _ _ _ _ _ eval).
    rewrite <- Exp_morph_com.
    repeat rewrite assoc.
    match goal with
      [|- _ = _ ∘ ?A ∘ ?M] =>
      match M with
          ?B ∘ ?D =>
          match B with
              (Prod_of _a (_, _) (_, _) (id, ?E)) =>
              match type of E with
                  Hom ?G ?H =>
                  match D with
                      (Prod_of _a (_, _) (_, _) ( ?F, id)) =>
                      match type of F with
                          Hom ?I ?J =>
                          cutrewrite (M = (Prod_of _a (_, _) (_, _) (F, id)) ∘ (Prod_of _a (_, _) (_, _) (@id _ I, E)))
                      end
                  end
              end
          end
      end
    end.
    {
      match goal with
          [|- _ = _ ∘ ?A ∘ ?B ∘ ?C] =>
          reveal_comp A B
      end.
      rewrite <- Exp_morph_com.
      repeat rewrite assoc.
      rewrite <- F_compose.
      simpl; auto.
    }
    {
      repeat rewrite <- F_compose.
      simpl; simpl_ids; trivial.
    }      
  }
  {
    rewrite <- F_compose.
    simpl; auto.
  }
Qed.

(* Exponential_Functor defined *)

Class Has_Exponentials (C : Category) {hp : Has_Products C} : Type :=
{
  HE_exp : Obj → Obj → Obj;

  HE_exp_exp : ∀ a b, Exponential C hp a b (HE_exp a b);

  Exp_of := Exponential_Functor HE_exp HE_exp_exp;

  curry : forall {a b c : Obj}, @Hom C (Prod_of _o (a, b)) c → @Hom C a (Exp_of _o (b, c)) :=
    fun {a b c : Obj} (f : @Hom C (Prod_of _o (a, b)) c) =>
      @Exp_morph_ex _ _ _ _ _ (HE_exp_exp b c) _ f;

  uncurry : forall {a b c : Obj}, @Hom C a (Exp_of _o (b, c)) -> @Hom C (Prod_of _o (a, b)) c :=
    fun {a b c : Obj} (f : Hom a (Exp_of _o (b, c))) =>
      (@eval _ _ _ _ _ (HE_exp_exp b c)) ∘ (Prod_of _a (_, _) (_, _) (f, @id C b))
}.

Existing Instance HE_exp_exp.

Section Curry_UnCurry.

  Context  {C : Category} {HP : Has_Products C} {HE : Has_Exponentials C} {a b c : Obj}.

  Theorem curry_uncurry (f : Hom a (Exp_of _o (b, c))) : curry (uncurry f) = f.
  Proof.
    unfold curry, uncurry.
    eapply Exp_morph_unique.
    rewrite <- Exp_morph_com.
    reflexivity.
    trivial.
  Qed.

  Theorem uncurry_curry (f : Hom (Prod_of _o (a, b)) c) : uncurry (curry f) = f.
  Proof.
    unfold curry, uncurry.
    rewrite <- Exp_morph_com.
    reflexivity.
  Qed.

End Curry_UnCurry.


