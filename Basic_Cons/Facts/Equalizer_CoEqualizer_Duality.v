Require Import Category.Main.
Require Import Basic_Cons.Equalizer.
Require Import Basic_Cons.CoEqualizer.


Set Primitive Projections.

Set Universe Polymorphism.

Section CoEq_Eq.
  Context {C : Category} {a b c: Obj} (f g : Hom a b) (Eq : Equalizer C f g c).

  Program Instance Equalizer_op_CoEqualizer : CoEqualizer (C ^op) f g c :=
    {
      coequalizer_morph := @equalizer_morph _ _ _ _ _ c Eq;
      coequalizer_morph_com := @equalizer_morph_com _ _ _ _ _ c Eq;
      coequalizer_morph_ex := @equalizer_morph_ex _ _ _ _ _ c Eq;
      coequalizer_morph_ex_com := @equalizer_morph_ex_com _ _ _ _ _ c Eq;
      coequalizer_morph_unique := @equalizer_morph_unique _ _ _ _ _ c Eq
    }.

  Context {HE : Has_Equalizers C}.

End CoEq_Eq.

Section Has_Equalizer_op_Has_CoEqualizer.
  Context {C : Category} {HE : Has_Equalizers C}.

  Program Instance Has_Equalizer_op_Has_CoEqualizer : Has_CoEqualizers C ^op :=
    {
      CoEqualizer_of := λ _ _ f g, @Equalizer_of C _ _ _ f g;
      CoEqualizer_of_CoEqualizer := λ _ _ f g, Equalizer_op_CoEqualizer _ _ (@Equalizer_of_Equalizer C _ _ _ f g)
    }.

End Has_Equalizer_op_Has_CoEqualizer.

Section Eq_CoEq.
  Context {C : Category} {a b c: Obj} (f g : Hom a b) (CEq : CoEqualizer C f g c).

  Program Instance CoEqualizer_op_Equalizer : Equalizer (C ^op) f g c :=
    {
      equalizer_morph := @coequalizer_morph _ _ _ _ _ c CEq;
      equalizer_morph_com := @coequalizer_morph_com _ _ _ _ _ c CEq;
      equalizer_morph_ex := @coequalizer_morph_ex _ _ _ _ _ c CEq;
      equalizer_morph_ex_com := @coequalizer_morph_ex_com _ _ _ _ _ c CEq;
      equalizer_morph_unique := @coequalizer_morph_unique _ _ _ _ _ c CEq
    }.

End Eq_CoEq.

Section Has_CoEqualizer_op_Has_Equalizer.
  Context {C : Category} {HE : Has_CoEqualizers C}.

  Program Instance Has_CoEqualizer_op_Has_Equalizer : Has_Equalizers C^op :=
    {
      Equalizer_of := λ _ _ f g, @CoEqualizer_of C _ _ _ f g;
      Equalizer_of_Equalizer := λ _ _ f g, CoEqualizer_op_Equalizer _ _ (@CoEqualizer_of_CoEqualizer C _ _ _ f g)
    }.

End Has_CoEqualizer_op_Has_Equalizer.
