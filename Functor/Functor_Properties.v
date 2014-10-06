Require Import Category.Core.
Require Import Functor.Functor.
Require Import Functor.Tactics.

Section Functor_Properties.
  Context `{C : Category Obj Hom} `{C' : Category Obj' Hom'} (F : Functor C C').

  Definition Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c = c'.

  Definition Essentially_Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c ≡ c'.
  
  Definition Surjective_Func := ∀ (c : Obj'), {c' : Obj | F _o c' = c}.

  Definition Essentially_Surjective_Func := ∀ (c : Obj'), {c' : Obj & F _o c' ≡ c}.
  
  Definition Faithful_Func := ∀ (c c' : Obj) (h h' : Hom c c'), F _a _ _ h = F _a _ _ h' → h = h'.
  
  Definition Full_Func := ∀ (c1 c2 : Obj) (h' : Hom' (F _o c1) (F _o c2)), {h : Hom c1 c2 | F _a _ _ h = h'}.

  Theorem Fully_Faithful_Essentially_Injective : Faithful_Func → Full_Func → Essentially_Injective_Func.
  Proof.
    intros F_Faithful F_Full c c' H.
    destruct (F_Full _ _ (
                       match H in (_ = Y) return Hom' (F _o c) Y with
                         | eq_refl => F _a _ _ (@id _ _ _ c)
                       end)
             ) as [U' HU].
    destruct (F_Full _ _ (
                       match H in (_ = Y) return Hom' Y (F _o c) with
                         | eq_refl => F _a _ _ (@id _ _ _ c)
                       end)
             ) as [V' HV].
    exists U'; exists V'.
    {
      apply F_Faithful.
      rewrite F_compose.
      rewrite HU, HV.
      repeat rewrite F_id.
      clear.
      destruct H.
      auto.
    }
    {
      apply F_Faithful.
      rewrite F_compose.
      rewrite HU, HV.
      repeat rewrite F_id.
      clear.
      destruct H.
      auto.
    }
  Qed.

  Theorem Fully_Faithful_Guarantees_Isos : Faithful_Func → Full_Func → ∀ (c c' : Obj), F _o c ≡ F _o c' → c ≡ c'.
  Proof.
    intros F_Faithful F_Full c c' [f [g H1 H2]].
    destruct (F_Full _ _ f) as [Ff Hf].
    destruct (F_Full _ _ g) as [Fg Hg].
    exists Ff; exists Fg.
    {
      apply F_Faithful.
      rewrite F_compose.
      rewrite Hf, Hg, F_id.
      trivial.
    }
    {
      apply F_Faithful.
      rewrite F_compose.
      rewrite Hf, Hg, F_id.
      trivial.
    }
  Qed.

  (**
  An embedding is a functor that is faully-faithful. Such a functor is necessarily essentially injective and also guarantees isomorphisms, i.e., if F __O c === F __O c' then c === c'.
   *)

  Class Embedding : Type :=
    {
      F_Faithful : Faithful_Func;
      
      F_Full : Full_Func;

      F_Essentially_Injective := Fully_Faithful_Essentially_Injective F_Faithful F_Full;

      F_Guarantees_Isos := Fully_Faithful_Guarantees_Isos F_Faithful F_Full
    }.

End Functor_Properties.
