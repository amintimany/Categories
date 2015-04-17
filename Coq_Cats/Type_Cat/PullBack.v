Require Import Category.Main.
Require Import Basic_Cons.CCC Basic_Cons.PullBack.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Section PullBack.
  Context {A B C : Type} (f : A → C) (g : B → C).

  Local Hint Extern 1 => match goal with [x : sig _ |- _ ] => let H := fresh "H" in destruct x as [x H] end.
  
  Program Instance Type_Cat_PullBack : @PullBack Type_Cat _ _ _ f g :=
    {
      pullback := {x : A * B| f (fst x) = g (snd x)};
      pullback_morph_1 := fun z => (fst (proj1_sig z));
      pullback_morph_2 := fun z => (snd (proj1_sig z));
      pullback_morph_ex := fun x p1 p2 H x' => (exist _ (p1 x', p2 x') _)
    }.

  Next Obligation.
  Proof.  
    exact (equal_f H x').
  Qed.    

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.  
    intros X p1 p2 H u u' H1 H2 H3 H4.
    destruct H3; destruct H4.
    extensionality x.
    set (H1x := equal_f H1 x); clearbody H1x; clear H1.
    set (H2x := equal_f H2 x); clearbody H2x; clear H2.
    cbn in *.
    match goal with
      [|- ?A = ?B] => destruct A as [[a1 a2] Ha]; destruct B as [[b1 b2] Hb]
    end.
    cbn in *.
    apply sig_proof_irrelevance; cbn.
    rewrite H1x; rewrite H2x; trivial.
  Qed.

End PullBack.

Instance Type_Cat_Has_PullBacks : Has_PullBacks Type_Cat := fun a b c f g => Type_Cat_PullBack f g.