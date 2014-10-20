Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Tactics.

(* Opposite Functor *)
Section Opposite_Functor.
  Context `{C : Category Obj Hom} `{D : Category Obj' Hom'} (F : Functor C D).

  Program Instance Opposite_Functor : Functor C^op D^op :=
    {
      FO := F _o;
      FA := λ a b h, F _a b a h;
      F_id := λ a, @F_id _ _ _ _ _ _ F a;
      F_compose := λ a b c f g, @F_compose _ _ _ _ _ _ F c b a g f
    }.

End Opposite_Functor.

Section Opposite_Opposite_Functor.
  Context `{C : Category Obj Hom} `{D : Category Obj' Hom'} (F : Functor C D).
  
  Theorem Opposite_Opposite_Functor : 
    F = 
    match (C_OP_OP C) in (_ = Y) return Functor Y _ with
        eq_refl =>
        match (C_OP_OP D) in (_ = Z) return Functor _ Z with
            eq_refl => Opposite_Functor (Opposite_Functor F)
        end
    end.
    destruct C; destruct D; destruct F; reflexivity.
  Defined.

  Theorem Functor_Opposite_Opposite : 
    Opposite_Functor (Opposite_Functor F) = 
    match eq_sym (C_OP_OP C) in (_ = Y) return Functor Y _ with
        eq_refl =>
        match eq_sym (C_OP_OP D) in (_ = Z) return Functor _ Z with
            eq_refl => F
        end
    end.
    destruct C; destruct D; destruct F; reflexivity.
  Defined.

End Opposite_Opposite_Functor.

(* Functor composition *)

Section Functor_Compose.

  Context `{C : Category Obj Hom} `{C' : Category Obj' Hom'} `{C'' : Category Obj'' Hom''} (F : Functor C C') (F' : Functor C' C'').

  Program Instance Functor_compose : Functor C C'' :=
    {
      FO := fun c => F' _o (F _o c);
      FA := fun c d f => F' _a _ _ (F _a _ _ f)
    }.
  
(* Functor_compose defined. *)

End Functor_Compose.

(* Associativity of functor composition *)

Section Functor_Assoc.
    Context `{C1 : Category Obj1 Hom1} `{C2 : Category Obj2 Hom2} `{C3 : Category Obj3 Hom3} `{C4 : Category Obj4 Hom4} (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4).

  Theorem Functor_assoc :
    (Functor_compose F (Functor_compose G H)) = (Functor_compose (Functor_compose F G) H).
  Proof.
    apply Functor_eq_simplify.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

End Functor_Assoc.

(* Identitiy functor *)

Program Instance Functor_id `{C : Category Obj Hom} : Functor C C :=
  {
    FO := fun x => x;
    FA := fun c d f => f
  }.

  (* Functor_id defined -- the rest of the obligations are taken care of by Program system *)

Section Functor_Identity_Unit.
  Context  `(C : Category Obj Hom) `(C' : Category Obj' Hom') (F : Functor C C').

  Theorem Functor_id_unit_left : (Functor_compose F Functor_id) = F.
  Proof.
    apply Functor_eq_simplify; simpl; trivial.
  Qed.

  Theorem Functor_id_unit_right : (Functor_compose Functor_id F) = F.
  Proof.
    apply Functor_eq_simplify; simpl; trivial.
  Qed.

End Functor_Identity_Unit.

