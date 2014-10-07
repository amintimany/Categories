Require Import Coq.Logic.EqdepFacts.

Require Import Category.Core.
Require Import Functor.Core.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.
Require Import Basic_Cons.Product.
Require Export Essentials.Types.

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

Local Obligation Tactic := idtac.

Program Instance Cat_Products (C : CAT) (C' : CAT) : Product Cat C C' (mkCAT _ _ (Prod_Cat (THE_CAT C) (THE_CAT C'))) :=
{
  Pi_1 := Prod_Cat_proj1 (THE_CAT C) (THE_CAT C');
  Pi_2 := Prod_Cat_proj2 (THE_CAT C)(THE_CAT C');

  Prod_morph_ex := fun P => fun F G => Prod_Cat_morph_ex (THE_CAT C) (THE_CAT C') (THE_CAT P) F G
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
  program_simpl.
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
      eapply FA_equal_f in H1; trivial.
      eapply FA_equal_f in H3; trivial.
      match goal with
          [|- (?A, ?B) ~= (?C, ?D)] =>
          cut (A ~= C); [intros HU; rewrite HU; cut (B ~= D); [intros HU'; rewrite HU'; trivial| symmetry; exact H3]| symmetry; exact H1]
      end.
    }
  }      
  {
    extensionality x.
    apply (fun p => equal_f p x) in H0; apply (fun p => equal_f p x) in H2.
    simpl in H0, H2; simpl.
    match goal with
        [|- ?A = ?B] =>
        destruct A; destruct B; simpl in H0, H2; subst; trivial
    end.
  }
Qed.


(* Cat_Products defined *)

Instance Cat_Has_Products : Has_Products Cat :=
{
  HP_prod := fun C C' => (mkCAT _ _ (Prod_Cat (THE_CAT C) (THE_CAT C')));
  HP_prod_prod := Cat_Products
}.




