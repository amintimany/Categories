Require Import Category.Main.
Require Import Category.Composable_Chain.
Require Import Functor.Functor.

Section Functor_Image.
  Context `{C : Category Obj Hom}
          `{D : Category Obj' Hom'}
          (F : Functor C D).

  Program Definition Functor_Image :=
    SubCategory D
                (λ a, ∃ x, F _o x = a)
                (
                  λ a b f,
                  ∃ (ch : Composable_Chain D a b),
                    (Compose_of ch) = f
                    ∧
                    Forall_Links ch (
                      λ x y g,
                      ∃ (c d : Obj) (h : Hom c d)
                        (Fca : F _o c = x) (Fdb : F _o d = y),
                        match Fca in (_ = Z) return Hom' Z _ with
                            eq_refl =>
                            match Fdb in (_ = Y) return Hom' _ Y with
                                eq_refl => F _a _ _ h
                            end
                        end = g)
                )
                _ _.
  
  Next Obligation. (* Hom_Cri_id *)
  Proof.
    exists (Single (F _a _ _ id)); simpl; split; auto.
    do 3 eexists; do 2 exists eq_refl; reflexivity.
  Qed.

  Next Obligation. (* Hom_Cri_compose *)
  Proof.
    match goal with
        [ch1 : Composable_Chain _ ?a ?b, ch2 : Composable_Chain _ ?b ?c|- _] =>
        exists (Chain_Compose ch1 ch2); split
    end.
    rewrite <- Compose_of_Chain_Compose; trivial.
    apply Forall_Links_Chain_Compose; auto.
  Qed.

End Functor_Image.

