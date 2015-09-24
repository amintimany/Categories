Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Basic_Cons.PullBack Basic_Cons.Terminal.

(**
A subobject classifier Ω is the object that classifies subobjects of all objects. That is,
There is a one to one correspondence between subobjects of an object a i.e., monomorphisms
 to a, m : x ≫–> a, and morphisms from a to Ω. It is formally defined as follows:

Ω together with ⊤ : 1 → Ω (1 is the terminal object) is a subobject classifier if we have
for any monomorphism m : a ≫–> b there is a unique morphism χₘ : b → Ω such that the
following diagram is a pullback:
#
<pre>
                !
        a ————————————–> 1
        |__|             |
        |                |
     m  |                |⊤
        |                |
        ↓                ↓
        b ————————————–> Ω
               χₘ  
</pre>
#

Where ! is the unique arrow to the terminal object.
*)
Section SubObject_Classifier.
  Context (C : Category) {term : Terminal C}.

  Record SubObject_Classifier : Type :=
    {
      SOC : C;
      SOC_morph : (term –≻ SOC)%morphism;
      SOC_char {a b : C} (m : (a ≫–> b)%morphism) : (b –≻ SOC)%morphism;
      SO_pulback {a b : C} (m : (a ≫–> b)%morphism) :
        is_PullBack
          (mono_morphism m)
          (t_morph term a)
          (SOC_char m)
          SOC_morph;
      SOC_char_unique {a b : C} (m : (a ≫–> b)%morphism) (h h' : (b –≻ SOC)%morphism) :
        is_PullBack
          (mono_morphism m)
          (t_morph term a)
          h
          SOC_morph
        →
        is_PullBack
          (mono_morphism m)
          (t_morph term a)
          h'
          SOC_morph
        →
        h = h'
    }.

  
End SubObject_Classifier.