Require Import Category.Main.
Require Import Basic_Cons.PullBack Basic_Cons.Terminal.

Section SubObject_Classifier.
  Context (C : Category) {term : Terminal C}.

  Class SubObject_Classifier : Type :=
    {
      SOC : C;
      SOC_morph : Monic term SOC;
      SOC_char {a b : C} (m : Monic a b) : Hom b SOC;
      SO_pulback {a b : C} (m : Monic a b) : is_PullBack (mono_morphism m) (t_morph term a) (SOC_char m) (mono_morphism SOC_morph);
      SOC_char_unique {a b : C} (m : Monic a b) (h h' : Hom b SOC) : is_PullBack (mono_morphism m) (t_morph term a) h (mono_morphism SOC_morph) → is_PullBack (mono_morphism m) (t_morph term a) h' (mono_morphism SOC_morph) → h = h'
    }.

End SubObject_Classifier.