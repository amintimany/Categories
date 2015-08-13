Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Archetypal.Discr.Discr Archetypal.Discr.NatFacts.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Cat.Cat_Iso.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import KanExt.LocalFacts.NatIso.

Require Import Limits.Limit.
Require Import Limits.Isomorphic_Cat.

Section GenProd_Sum.
  Context {A : Type} {C : Category} (map : A → C).

  Definition GenProd := Limit (Discr_Func map).

  Identity Coercion GenProd_Limit : GenProd >-> Limit.
  
  Definition GenSum := CoLimit (Discr_Func_op map).

  Identity Coercion GenSum_CoLimit : GenSum >-> CoLimit.

End GenProd_Sum.



(** The fact That if a category has generalized products of some type, its dual also has
generalized sums of that type. *)

Section GenProd_to_GenSum.
  Context {A : Type} {C : Category} {map : A → C} (L : GenProd map).  
  Definition GenProd_to_GenSum : @GenSum A (C^op) map :=
    Local_Right_KanExt_Iso ((@Discr_Func_Iso (C^op) A map)⁻¹) L.

End GenProd_to_GenSum.

(** The fact That if a category has generalized sums of some type, its dual has
generalized products of that type. *)
Section GenSum_to_GenProd.
  Context {A : Type} {C : Category} {map : A → C} (L : GenSum map).
  
  Definition GenSum_to_GenProd : @GenProd A (C^op) map :=
    Local_Right_KanExt_Iso (Discr_Func_Iso map) L.

End GenSum_to_GenProd.

(** If we have GenSum for all functions from a type A, where A is isomorphic to B
we have all GenSum for all functions from B – we can't use this proof as it involves
isomorphism of categories (Discr_Cat A ≡ Discr_Cat B). This, given current semantics of
Coq's universe polymorphism implies (Discr_Cat A), (Discr_Cat B) and C must be at the same
universe levels which is inconsistent when used to prove cocompleteness of
Type_Cat. *)
(**
#
<pre>
Section GenSum_IsoType.
  Context {A B : Type} (Iso : (A ≡≡ B ::> Type_Cat)%morphism) {C : Category}
          (SM : forall f : A → C, GenSum f).

  Program Definition GenSum_IsoType_map_Iso (map : B → C):
    (
      ((Discr_Func_op map)^op)%functor
        ≡≡ ((Discr_Func_op (fun x : A => map ((iso_morphism Iso) x)) ∘ (iso_morphism (Opposite_Cat_Iso (Inverse_Isomorphism (Discr_Cat_Iso Iso)))))^op)%functor
        ::> Func_Cat _ _
    )%morphism
    :=
      {|
        iso_morphism :=
          {|
            Trans :=
              Trans
                (iso_morphism
                   (IsoCat_NatIso (Opposite_Cat_Iso (Discr_Cat_Iso Iso)) (Discr_Func_op map))
                )
          |};
        inverse_morphism :=
          {|
            Trans :=
              Trans
                (inverse_morphism
                   (IsoCat_NatIso (Opposite_Cat_Iso (Discr_Cat_Iso Iso)) (Discr_Func_op map))
                )
          |}
      |}
  .

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    apply (
        f_equal
          Trans
          (
            right_inverse
              (IsoCat_NatIso (Opposite_Cat_Iso (Discr_Cat_Iso Iso)) (Discr_Func_op map))
          )
      ).
  Qed.
  
  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    apply (
        f_equal
          Trans
          (
            left_inverse
              (IsoCat_NatIso (Opposite_Cat_Iso (Discr_Cat_Iso Iso)) (Discr_Func_op map))
          )
      ).
  Qed.
  
  Definition  GenSum_IsoType (map : B → C) : GenSum map :=
    Local_Right_KanExt_Iso
      (GenSum_IsoType_map_Iso map)
      (
        CoLimit_From_Isomorphic_Cat
          (Opposite_Cat_Iso (Inverse_Isomorphism (Discr_Cat_Iso Iso)))
          (SM (fun x : A => map ((iso_morphism Iso) x)))
      ).

End GenSum_IsoType.
</pre>
#
*)

(** This alternative proof is a direct one and thus does not impose undesirable
universe restrictions. *)
Section GenSum_GenProd_IsoType.
  Context {A B : Type}
          (Iso : (A ≃≃ B ::> Type_Cat)%isomorphism)
  .

  Section Conversions.
    Context {C : Category} {f : B → C}.

    Section GenProd_IsoType_Cone_Conversion_1.
      Context (Cn : Cone (Discr_Func (f ∘ (iso_morphism Iso)))%morphism).
      
      Program Definition GenProd_IsoType_Cone_Conversion_1 : Cone (Discr_Func f) :=
        {|
          cone_apex := Cn;
          cone_edge :=
            {|
              Trans :=
                fun c =>
                  match equal_f (right_inverse Iso) c in _ = u return
                        (((Cn _o) tt)%object –≻ (f u))%morphism with
                    eq_refl => Trans Cn ((inverse_morphism Iso) c)
                  end
            |}
        |}.

    End GenProd_IsoType_Cone_Conversion_1.
  
    Section GenProd_IsoType_Cone_Conversion_2.
      Context (Cn : Cone (Discr_Func f)).

      Program Definition GenProd_IsoType_Cone_Conversion_2 : Cone (Discr_Func (f ∘ (iso_morphism Iso))%morphism) :=
        {|
          cone_apex := Cn;
          cone_edge :=
            {|
              Trans :=
                fun c =>Trans Cn ((iso_morphism Iso) c)
            |}
        |}.

    End GenProd_IsoType_Cone_Conversion_2.

    Section GenProd_IsoType_Cone_Conversion_1_2.
      Context (Cn : Cone (Discr_Func (f ∘ (iso_morphism Iso)))%morphism).

      Theorem GenProd_IsoType_Cone_Conversion_1_2 : GenProd_IsoType_Cone_Conversion_2 (GenProd_IsoType_Cone_Conversion_1 Cn) = Cn.
      Proof.
        unfold GenProd_IsoType_Cone_Conversion_1, GenProd_IsoType_Cone_Conversion_2.
        destruct Cn.
        cbn.
        match goal with
          [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
        end.
        apply NatTrans_eq_simplify; extensionality c; cbn.
        apply JMeq_eq.
        destruct equal_f.
        cbn_rewrite (equal_f (left_inverse Iso) c); trivial.
      Qed.

    End GenProd_IsoType_Cone_Conversion_1_2.

    Section GenProd_IsoType_Cone_Conversion_2_1.
      Context (Cn : Cone (Discr_Func f)).

      Theorem GenProd_IsoType_Cone_Conversion_2_1 : GenProd_IsoType_Cone_Conversion_1 (GenProd_IsoType_Cone_Conversion_2 Cn) = Cn.
      Proof.
        unfold GenProd_IsoType_Cone_Conversion_1, GenProd_IsoType_Cone_Conversion_2.
        destruct Cn.
        cbn.
        match goal with
          [|- {| cone_edge := ?A |} = {| cone_edge := ?B |} ] => cutrewrite (A = B); trivial
        end.
        apply NatTrans_eq_simplify; extensionality c; cbn.
        destruct equal_f; trivial.
      Qed.

    End GenProd_IsoType_Cone_Conversion_2_1.

    Section GenProd_IsoType_Cone_Morph_Conversion_1.
      Context {Cn Cn' : Cone (Discr_Func (f ∘ (iso_morphism Iso)))%morphism} (h : Cone_Morph _ Cn Cn').

      Program Definition GenProd_IsoType_Cone_Morph_Conversion_1 : Cone_Morph (Discr_Func f) (GenProd_IsoType_Cone_Conversion_1 Cn) (GenProd_IsoType_Cone_Conversion_1 Cn') :=
        {|
          cone_morph := h
        |}.

      Next Obligation.
      Proof.
        apply NatTrans_eq_simplify; extensionality x; cbn.
        destruct equal_f.
        apply (
            f_equal
              (fun w :
                     ((Cn ∘ (Functor_To_1_Cat (Discr_Cat A)))
                        –≻ (Discr_Func (f ∘ (iso_morphism Iso))%morphism))%nattrans
               =>
                 Trans w (inverse_morphism Iso x)
              )
              (cone_morph_com h)
          )
        .
      Qed.

    End GenProd_IsoType_Cone_Morph_Conversion_1.
  
    Section GenProd_IsoType_Cone_Morph_Conversion_2. 
      Context {Cn Cn' : Cone (Discr_Func f)} (h : Cone_Morph _ Cn Cn').

      Program Definition GenProd_IsoType_Cone_Morph_Conversion_2 : Cone_Morph (Discr_Func (f ∘ (iso_morphism Iso))%morphism) (GenProd_IsoType_Cone_Conversion_2 Cn) (GenProd_IsoType_Cone_Conversion_2 Cn') :=
        {|
          cone_morph := h
        |}.

      Next Obligation.
      Proof.
        apply NatTrans_eq_simplify; extensionality x; cbn.
        apply (
            f_equal
              (fun w :
                     ((Cn ∘ (Functor_To_1_Cat (Discr_Cat B)))
                       –≻ (Discr_Func f))%nattrans
               =>
                 Trans w (iso_morphism Iso x)
              )
              (cone_morph_com h)
          )
        .
      Qed.

    End GenProd_IsoType_Cone_Morph_Conversion_2.

  End Conversions.
    
  Section GenProd_IsoType.
    Context {C : Category} (H : forall f : A → C, GenProd f).
  
    Program Definition GenProd_IsoType (map : B → C) : GenProd map :=
      {|
        LRKE := GenProd_IsoType_Cone_Conversion_1 (H (map ∘ (iso_morphism Iso))%morphism);
        LRKE_morph_ex :=
          fun Cn =>
            match GenProd_IsoType_Cone_Conversion_2_1 Cn in _ = y return
                  LoKan_Cone_Morph y _
            with
              eq_refl =>
              GenProd_IsoType_Cone_Morph_Conversion_1
                (
                  LRKE_morph_ex
                    (H (map ∘ (iso_morphism Iso))%morphism)
                    (GenProd_IsoType_Cone_Conversion_2 Cn)
                )
            end;
        LRKE_morph_unique := fun Cn h h' => _
      |}.

    Next Obligation.
    Proof.
      set (Wh := GenProd_IsoType_Cone_Morph_Conversion_2 h).
      set (Wh' := GenProd_IsoType_Cone_Morph_Conversion_2 h').
      set (M := LRKE_morph_unique (H (map ∘ Iso)%morphism)).
      rewrite <- (GenProd_IsoType_Cone_Conversion_1_2 (LRKE (H (map ∘ Iso)%morphism))) in M.
      set (M' := M _ Wh Wh').
      change (cone_morph h) with (cone_morph Wh).
      change (cone_morph h') with (cone_morph Wh').
      destruct M; trivial.
    Qed.

  End GenProd_IsoType.

  Section GenSum_IsoType.
  Context {C : Category} (H : forall f : A → C, GenSum f).
  
  Definition  GenSum_IsoType (map : B → C) : GenSum map :=
    GenProd_to_GenSum
      (GenProd_IsoType
         (fun f : A → (C ^op)%category => GenSum_to_GenProd (H f))
         map
      )
  .

  End GenSum_IsoType.

End GenSum_GenProd_IsoType.