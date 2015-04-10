Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Limits.Limit.
Require Import Archetypal.Discr.
Require Import Basic_Cons.Terminal.

Section Type_Cat_Gen_Prod.
  Context (A : Type) (map : A → Type).

  Local Notation Fm := (Discrete_Functor Type_Cat map) (only parsing).

  Program Instance Type_Cat_Gen_Prod_Cone : Cone Fm :=
    {|
      cone_apex := {|FO := fun _ => ∀ x : A, Fm _o x; FA := fun _ _ _ h => h|};
      cone_edge := {|Trans := fun x y => y x |}
    |}.

  Program Instance Type_Cat_Gen_Sum : Limit Fm :=
    {|
      LRKE := Type_Cat_Gen_Prod_Cone;
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|Trans :=
                  fun c X x  =>
                    match c as u return ((Cn _o) u → map x) with
                    | tt => fun X : (Cn _o) tt => Trans Cn x X
                    end X
              |}
          |}
    |}.

  Next Obligation.
  Proof.
    destruct c; destruct c'; destruct h.
    extensionality x; extensionality y.
    set (H := equal_f ((@Trans_com _ _ _ _ Cn) y y (Discr_id _ _)) x).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Type_Cat_Gen_Sum_obligation_1.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y; extensionality z.
    destruct x.
    set (hc := (cone_morph_com h')).
    rewrite (cone_morph_com h) in hc.
    set (hc' := (f_equal (fun w : NatTrans
                  (Functor_compose (Functor_To_1_Cat (Discr_Cat A)) Cn)
                  (Discrete_Functor Type_Cat map) =>
           Trans w z y) hc)); clearbody hc'; clear hc.
    trivial.
  Qed.    

End Type_Cat_Gen_Prod.