Require Import Category.Main.
Require Import Topos.SubObject_Classifier.
Require Import Basic_Cons.Terminal Basic_Cons.PullBack.
Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.
Require Import Coq.Logic.ChoiceFacts.
Require Coq.Logic.ClassicalFacts.
Local Obligation Tactic := idtac.

Local Axiom PropExt : ClassicalFacts.prop_extensionality.
Local Axiom ConstructiveIndefiniteDescription_Type : forall T : Type, ConstructiveIndefiniteDescription_on T.

Section Type_Cat_characteristic_function_unique.
  Context {A B : Type} (F : @Monic Type_Cat A B) (h h' : B → Prop) (hpb : is_PullBack (mono_morphism F) (fun _ => TT) h (fun _ => True)).

  Theorem Type_Cat_characteristic_function_unique : h = fun x => (exists y : A, (mono_morphism F) y = x).
  Proof.
    extensionality x.
    apply PropExt; split.
    {
      intros Hx.
      set (M := fun w : (A + UNIT)%type =>
                   match w with
                   | inl m => mono_morphism F m
                   | inr _ => x
                   end).
      cut ((fun x => h (M x)) = (fun _ => True)).
      {
        intros H.
        set (W := equal_f (is_pullback_morph_ex_com_1 hpb (A + UNIT)%type M (fun _ => TT) H) (inr TT)).
        cbn in W.
        eexists; exact W.
      }
      extensionality y; destruct y as [y|]; cbn.
      {      
        apply (equal_f (is_pullback_morph_com hpb)).
      }
      {
        apply PropExt; split; trivial.
      }
    }
    {
      intros [y []].
      set (W := (equal_f (is_pullback_morph_com hpb))).
      cbn in W.
      rewrite W; trivial.
    }
  Qed.

End Type_Cat_characteristic_function_unique.


Program Instance Type_Cat_SubObject_Classifier : SubObject_Classifier Type_Cat :=
  {
    SOC := Prop;
    SOC_morph := {|mono_morphism := fun _ : UNIT => True|};
    SOC_char := fun A B f x => exists y : A, (mono_morphism f) y = x;
    SO_pulback :=
      fun A B f =>
        {|
          is_pullback_morph_ex :=
            fun p' pm1 pm2 pmc x => proj1_sig (ConstructiveIndefiniteDescription_Type A _ match eq_sym (equal_f pmc x) in _ = y return y with eq_refl => I end)
        |}
  }.

Next Obligation.
Proof.
  intros c g h H.
  extensionality x.
  apply UNIT_SINGLETON.
Qed.

Next Obligation.
Proof.
  intros A B f.
  extensionality x; cbn.
  apply PropExt; split; intros H; auto.
  exists x; trivial.
Qed.

Next Obligation.
Proof.
  intros A B f p' pm1 pm2 pmc.
  extensionality x; cbn in *.
  match goal with
    [|- mono_morphism f (proj1_sig ?A) = _ ] => destruct A as [y Hy]
  end.
  trivial.
Qed.    

Next Obligation.
Proof.
  intros A B f p' pm1 pm2 pmc.
  extensionality x.
  apply UNIT_SINGLETON.
Qed.  

Next Obligation.
Proof.
  intros A B f p' pm1 pm2 pmc u u' H1 _ H2 _.
  destruct H2.
  apply (mono_morphism_monomorphic f) in H1; trivial.
Qed.

Next Obligation.
Proof.
  intros A B f h h' PB1 PB2.
  cbn in *.
  etransitivity; [|symmetry]; apply Type_Cat_characteristic_function_unique; trivial.
Qed.