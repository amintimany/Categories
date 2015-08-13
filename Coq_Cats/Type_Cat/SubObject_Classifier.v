Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Topos.SubObject_Classifier.
Require Import Basic_Cons.Terminal Basic_Cons.PullBack.
Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.
Require Import Coq.Logic.ChoiceFacts.
Require Coq.Logic.ClassicalFacts.

Local Axiom PropExt : ClassicalFacts.prop_extensionality.
Local Axiom ConstructiveIndefiniteDescription_Type : forall T : Type, ConstructiveIndefiniteDescription_on T.

(** The type Prop is the subobject classifier for Type_Cat. With ⊤ mapping the single element of
the singleton set to (True : Prop) *)
Section Type_Cat_characteristic_function_unique.
  Context {A B : Type} (F : @Monic Type_Cat A B) (h h' : B → Prop) (hpb : is_PullBack (mono_morphism F) (fun _ => TT) h (fun _ => True)).

  Theorem Type_Cat_characteristic_function_unique : h = fun x => (exists y : A, (mono_morphism F) y = x).
  Proof.
    extensionality x.
    apply PropExt; split.
    {
      intros Hx.
      cut ((fun _ : UNIT => h x) = (fun _ => True)).
      {
        intros H.
        set (W := equal_f (is_pullback_morph_ex_com_1 hpb UNIT (fun _ => x) (fun _ => TT) H) TT).
        cbn in W.
        eexists; exact W.
      }
      {
        extensionality y; apply PropExt; split; trivial.
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


Local Hint Resolve UNIT_SINGLETON.

Program Definition Type_Cat_SubObject_Classifier : SubObject_Classifier Type_Cat :=
  {|
    SOC := Prop;
    SOC_morph := {|mono_morphism := fun _ : UNIT => True|};
    SOC_char := fun A B f x => exists y : A, (mono_morphism f) y = x;
    SO_pulback :=
      fun A B f =>
        {|
          is_pullback_morph_ex :=
            fun p' pm1 pm2 pmc x => proj1_sig (ConstructiveIndefiniteDescription_Type A _ match eq_sym (equal_f pmc x) in _ = y return y with eq_refl => I end)
        |}
  |}.

Next Obligation.
Proof.
  extensionality x.
  apply PropExt; split; intros H; auto.
  exists x; trivial.
Qed.

Next Obligation.
Proof.
  extensionality x.
  match goal with
    [|- mono_morphism ?f (proj1_sig ?A) = _ ] => destruct A as [y Hy]
  end.
  trivial.
Qed.    

Next Obligation.
Proof.
  match goal with
    [g : (_ ≫–> _)%morphism |- _] =>
    match goal with
      [H : (fun w => (mono_morphism g) (_ w)) = (fun x => (mono_morphism g) (_ x)) |- _] =>
      apply (mono_morphism_monomorphic g) in H
    end
  end.
  auto.
Qed.

Next Obligation.
Proof.
  etransitivity; [|symmetry]; eapply Type_Cat_characteristic_function_unique; eassumption.
Qed.