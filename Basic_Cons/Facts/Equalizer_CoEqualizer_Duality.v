Require Import Category.Main.
Require Import Basic_Cons.Equalizer.
Require Import Basic_Cons.CoEqualizer.


Set Primitive Projections.

Set Universe Polymorphism.

Section CoEq_Eq.
  Context {C : Category} {a b : C} (f g : Hom a b) (Eq : Equalizer f g).

  Program Instance Equalizer_op_CoEqualizer : @CoEqualizer (C ^op) _ _ f g :=
    {
      coequalizer := Eq;
      coequalizer_morph := @equalizer_morph _ _ _ _ _ Eq;
      coequalizer_morph_com := @equalizer_morph_com _ _ _ _ _ Eq;
      coequalizer_morph_ex := @equalizer_morph_ex _ _ _ _ _ Eq;
      coequalizer_morph_ex_com := @equalizer_morph_ex_com _ _ _ _ _ Eq;
      coequalizer_morph_unique := @equalizer_morph_unique _ _ _ _ _ Eq
    }.

End CoEq_Eq.

Section Has_Equalizer_op_Has_CoEqualizer.
  Context {C : Category} {HE : Has_Equalizers C}.

  Program Instance Has_Equalizer_op_Has_CoEqualizer : Has_CoEqualizers C^op :=
    {
      has_coequalizers := λ _ _ f g, @Equalizer_op_CoEqualizer _ _ _ _ _ (HE _ _ f g)
    }.

End Has_Equalizer_op_Has_CoEqualizer.

Section Eq_CoEq.
  Context {C : Category} {a b : C} (f g : Hom a b) (CEq : CoEqualizer f g).

  Program Instance CoEqualizer_op_Equalizer : @Equalizer (C ^op) _ _ f g :=
    {
      equalizer := CEq;
      equalizer_morph := @coequalizer_morph _ _ _ _ _ CEq;
      equalizer_morph_com := @coequalizer_morph_com _ _ _ _ _ CEq;
      equalizer_morph_ex := @coequalizer_morph_ex _ _ _ _ _ CEq;
      equalizer_morph_ex_com := @coequalizer_morph_ex_com _ _ _ _ _ CEq;
      equalizer_morph_unique := @coequalizer_morph_unique _ _ _ _ _ CEq
    }.

End Eq_CoEq.

Section Has_CoEqualizer_op_Has_Equalizer.
  Context {C : Category} {HE : Has_CoEqualizers C}.

  Program Instance Has_CoEqualizer_op_Has_Equalizer : Has_Equalizers C^op :=
    {
      has_equalizers := λ _ _ f g, @CoEqualizer_op_Equalizer _ _ _ _ _ (HE _ _ f g)
    }.

End Has_CoEqualizer_op_Has_Equalizer.
