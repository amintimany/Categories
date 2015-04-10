Require Import Category.Main.
Require Import Functor.Functor.

(* Opposite Functor *)
Section Opposite_Functor.
  Context {C D : Category} (F : Functor C D).

  Program Instance Opposite_Functor : Functor C^op D^op :=
    {
      FO := F _o;
      FA := fun _ _ h => F _a _ _ h;
      F_id := fun a => F_id F a;
      F_compose := fun _ _ _ f g => F_compose F g f
    }.

End Opposite_Functor.

(* Functor composition *)

Section Functor_Compose.

  Context {C C' C'' : Category} (F : Functor C C') (F' : Functor C' C'').

  Program Instance Functor_compose : Functor C C'' :=
    {
      FO := fun c => F' _o (F _o c);
      FA := fun c d f => F' _a _ _ (F _a _ _ f)
    }.
  
(* Functor_compose defined. *)

End Functor_Compose.

(* Associativity of functor composition *)

Section Functor_Assoc.
    Context {C1 C2 C3 C4 : Category} (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4).

  Theorem Functor_assoc :
    (Functor_compose F (Functor_compose G H)) = (Functor_compose (Functor_compose F G) H).
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; try destruct W; trivial
    end.
    extensionality x; extensionality y; extensionality f.
    match goal with
      [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
      transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
    end.
    destruct W; trivial.
    apply JMeq_eq.
    destruct W; trivial.
  Qed.

End Functor_Assoc.

(* Identitiy functor *)

Program Instance Functor_id (C : Category) : Functor C C :=
  {
    FO := fun x => x;
    FA := fun c d f => f
  }.

  (* Functor_id defined -- the rest of the obligations are taken care of by Program system *)

Section Functor_Identity_Unit.
  Context  (C C' : Category) (F : Functor C C').

  Theorem Functor_id_unit_left : (Functor_compose F (Functor_id _)) = F.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    extensionality x; extensionality y; extensionality f.
    match goal with
      [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
      transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
    end.
    destruct W; trivial.
    apply JMeq_eq.
    destruct W; trivial.
  Qed.

  Theorem Functor_id_unit_right : (Functor_compose (Functor_id _) F) = F.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    extensionality x; extensionality y; extensionality f.
    match goal with
      [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
      transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
    end.
    destruct W; trivial.
    apply JMeq_eq.
    destruct W; trivial.
  Qed.

End Functor_Identity_Unit.

