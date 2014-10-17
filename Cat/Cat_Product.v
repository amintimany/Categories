Require Import Coq.Logic.EqdepFacts.

Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.

Program Instance Prod_Cat_proj1 `(C : Category Obj Hom) `(C' : Category Obj' Hom') : Functor (Prod_Cat C C') C :=
{
  FO := fun x => fst x;
  FA := fun _ _ f => fst f
}.

(* Prod_Cat_Proj1 defined *)

Program Instance Prod_Cat_proj2 `(C : Category Obj Hom) `(C' : Category Obj' Hom') : Functor (Prod_Cat C C') C' :=
{
  FO := fun x => snd x;
  FA := fun _ _ f => snd f
}.

(* Prod_Cat_Proj2 defined *)


Program Instance Prod_Cat_morph_ex `(C : Category Obj Hom) `(C' : Category Obj' Hom') `(C'' : Category Obj'' Hom'') (F : Functor C''  C) (G : Functor C'' C') : Functor C'' (Prod_Cat C C') :=
{
  FO := fun x => (F _o x, G _o x);
  FA := fun _ _ f => (F _a _ _ f, G _a _ _ f)
}.

(* Prod_Cat_morph_ex defined *)

Local Obligation Tactic := idtac.

Program Instance Cat_Products (C : CAT) (C' : CAT) : Product Cat C C' (Prod_Cat C C') :=
{
  Pi_1 := Prod_Cat_proj1 C C';
  Pi_2 := Prod_Cat_proj2 C C';

  Prod_morph_ex := fun P => fun F G => Prod_Cat_morph_ex C C' P F G
}.

Next Obligation. (* Prod_morph_com1 *)
Proof.
  intros C C' p' r1 r2.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Next Obligation. (* Prod_morph_com2 *)
Proof.
  intros C C' p' r1 r2.
  apply Functor_eq_simplify; simpl; trivial.
Qed.

Next Obligation. (* Prod_morph_unique *)
Proof.
  intros C C' p' r1 r2 f g H1 H2 H3 H4.
  destruct H1; destruct H2.
  dependent destruction H3; dependent destruction H4.
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
      cut (fst A ~= fst B); [cut (snd A ~= snd B); [elim A; elim B; auto 2|]|]
      end;
        repeat
          match goal with
              [H : _ ≃ _|- _] =>
              (try (eapply (FA_equal_f _) in H; symmetry in H; eauto; fail) || clear H)
          end.
    }
  }      
  {
    extensionality z.
    apply (fun p => equal_f p z) in x1; apply (fun p => equal_f p z) in x2. 
    simpl in x1, x2; simpl.
    match goal with
        [|- ?A = ?B] =>
        destruct A; destruct B; simpl in x1, x2; subst; trivial
    end.
  }
Qed.


(* Cat_Products defined *)

Instance Cat_Has_Products : Has_Products Cat :=
{
  HP_prod := fun C C' => Prod_Cat C C';
  HP_prod_prod := Cat_Products
}.




