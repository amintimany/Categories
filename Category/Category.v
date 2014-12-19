Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Require Export Essentials.Notations.
Require Export Essentials.Tactics.

Set Primitive Projections.

Set Universe Polymorphism.

Class Category : Type :=
{
  (* Type of Objects *)
  Obj : Type;

  (* Type of morphism beween two objects *)
  Hom : Obj → Obj → Type;

  (* composition of morphisms: *)
  compose : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c where "f ∘ g" := (compose g f);

  (* associativity of composition: *)
  assoc : ∀ {a b c d : Obj} (f : Hom  a b) (g : Hom b c) (h : Hom c d),
                     ((h ∘ g) ∘ f) = (h ∘ (g ∘ f));

  (* symmetric form of associativity: *)
  assoc_sym : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
                     ((h ∘ (g ∘ f) = (h ∘ g) ∘ f));

  (* identity morphisms: *)
  id : ∀ {a : Obj}, Hom a a;

  (* id left unit: *)
  id_unit_left : ∀ (a b : Obj) (h : Hom a b), id ∘ h = h;

  (* id right unit: *)
  id_unit_right : ∀ (a b : Obj) (h : Hom a b), h ∘ id = h
}.

Notation "f ∘ g" := (compose g f) : morphism_scope.

Bind Scope category_scope with Category.

Bind Scope morphism_scope with Hom.

Coercion Obj : Category >-> Sortclass.

Hint Resolve id_unit_left id_unit_right.

Lemma Category_eq_simplify (C C' : Category) : @Obj C = @Obj C' → @Hom C ≃ @Hom C' → @compose C ≃ @compose C' → @id C ≃ @id C' → C = C'.
Proof.
  intros H1 H2 H3 H4.
  destruct C as [? ? Ccomp Cas Cass Cid Ciul Ciur]; destruct C' as [? ? Ccomp' Cas' Cass' Cid' Ciul' Ciur']; simpl in *.
  destruct H1.
  dependent destruction H2.
  dependent destruction H3.
  dependent destruction H4.
  destruct (proof_irrelevance _ Cas Cas').
  destruct (proof_irrelevance _ Cass Cass').
  destruct (proof_irrelevance _ Ciul Ciul').
  destruct (proof_irrelevance _ Ciur Ciur').
  reflexivity.
Qed.

(* basic tactics for categories *)

Ltac reveal_make_rightmost f term :=
  let rec RMR termx :=
      lazymatch termx with
        | (_ ∘ f) => apply (eq_refl termx)
        | (?A ∘ ?B) =>
          match type of $(RMR B)$ with
              _ = (?C ∘ f) =>
              exact (
                  eq_trans
                  (match $(RMR B)$ in _ = Y return termx = A ∘ Y with
                      eq_refl => eq_refl
                  end)
                    (assoc_sym f C A)
                )
          end
        | _ => fail
      end
  in
  RMR term.

Ltac reveal_make_leftmost f term :=
  let rec RML termx :=
      lazymatch termx with
        | (f ∘ _) => apply (eq_refl termx)
        | (?A ∘ ?B) =>
          match type of $(RML A)$ with
              _ = (f ∘ ?C) =>
              exact (
                  eq_trans
                  (match $(RML A)$ in _ = Y return termx = Y ∘ B with
                      eq_refl => eq_refl
                  end)
                    (assoc B C f)
                )
          end
        | _ => fail
      end
  in
  RML term.

Ltac reveal_prepare_equality_term f g A B term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = ?C ∘ f =>
      match type of $(reveal_make_leftmost g B)$ with
          _ = g ∘ ?D =>
          exact (eq_trans
                   (match $(reveal_make_rightmost f A)$ in _ = X return term = X ∘ _ with
                        eq_refl =>
                        match $(reveal_make_leftmost g B)$ in _ = Y return term = _ ∘ Y with
                            eq_refl => eq_refl
                        end
                    end)
                   (eq_trans
                       (assoc (g ∘ D) f C)
                       (match assoc_sym D g f in _ = Z return C ∘ f ∘ g ∘ D = C ∘ Z with
                            eq_refl => eq_refl
                        end)
                   )
                )
      end
  end
.

Ltac reveal_prepare_equality_term_left_explicit f g B term :=
  match type of $(reveal_make_leftmost g B)$ with
      _ = g ∘ ?D =>
      exact (eq_trans
               (
                 match $(reveal_make_leftmost g B)$ in _ = Y return term = _ ∘ Y with
                     eq_refl => eq_refl
                 end
               )
               (assoc_sym D g f)
            )
  end
.

Ltac reveal_prepare_equality_term_right_explicit f g A term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = ?C ∘ f =>
      exact (eq_trans
               (
                 match $(reveal_make_rightmost f A)$ in _ = Y return term = Y ∘ _ with
                     eq_refl => eq_refl
                 end
               )
               (assoc g f C)
            )
  end
.

Ltac reveal_comp_in_goal f g :=
  match goal with
    | [|- context[?term]] =>
      match term with
        | f ∘ g => idtac
        | ?A ∘ ?B =>
          rewrite $(reveal_prepare_equality_term f g A B term)$
        | f ∘ ?B =>
          rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$
        | ?A ∘ g =>
          rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$
      end
    | _ => fail
  end.

Ltac reveal_comp_in_I f g I :=
  match type of I with
    | context[?term] =>
      match term with
        | f ∘ g => idtac
        | ?A ∘ ?B =>
          rewrite $(reveal_prepare_equality_term f g A B term)$ in I
        | f ∘ ?B =>
          rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$ in I
        | ?A ∘ g =>
          rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$ in I
      end
    | _ => fail
  end.

Tactic Notation "reveal_comp" constr(f) constr(g) := reveal_comp_in_goal f g.

Tactic Notation "reveal_comp" constr(f) constr(g) "in" hyp(I) := reveal_comp_in_I f g I.

(*
Goal (∀ (C : Category) (a : C) (f g h i : Hom a a), (f ∘ (g ∘ (f ∘ g))) ∘ ((h ∘ i) ∘ (h ∘ i)) = f ∘ g ∘ f ∘ g ∘ h ∘ i ∘ h ∘ i).
intros.
reveal_comp g h.
reveal_comp f g.
reveal_comp g f.
reveal_comp i h.
reveal_comp h i.


Unset Ltac Debug.
rewrite $(reveal_prepare_equality_term g h (f ∘ g ∘ f ∘ g) ((h ∘ i) ∘ h ∘ i) )$.

set (H := $(reveal_prepare_equality_term g h (f ∘ g ∘ f ∘ g) ((h ∘ i) ∘ h ∘ i) )$).
clearbody H.
*)


(*
Ltac reveal_comp_in_goal f g :=
  match goal with
    | [ |- context[f ∘ g] ] => idtac
    | [ |- context[?B ∘ (?A ∘ f)] ] =>
      rewrite <- (assoc f _ _)
    | [ |- context[((g ∘ ?A) ∘ ?B)] ] =>
      rewrite (assoc _ _ g)
    | [ |- context[(?A ∘ f) ∘ (g ∘ ?B)] ] =>
      rewrite <- (assoc _ g (_ ∘ f))
    | [ |- context[((?A ∘ f) ∘ g)] ] =>
      rewrite (assoc g f)
    | [ |- context[(f ∘ (g ∘ ?B))] ] =>
      rewrite <- (assoc _ g f)
  end;
  match goal with
    | [ |- context[f ∘ g] ] => idtac
    | _ => reveal_comp_in_goal f g
  end
.

Ltac reveal_comp_in_I f g I :=
  match type of I with
    | context[f ∘ g] => idtac
    | context[?B ∘ (?A ∘ f)] =>
      let J := fresh "H" in
      assert (J := assoc f A B); rewrite <- J in I; clear J
    | context[((g ∘ ?A) ∘ ?B)] =>
      let J := fresh "H" in
      assert (J := assoc B A g); rewrite J in I; clear J
    | context[(?A ∘ f) ∘ (g ∘ ?B)] =>
      let J := fresh "H" in
      assert (J := assoc B g (A ∘ f)); rewrite <- J in I; clear J
    | context[((?A ∘ f) ∘ g)] =>
      let J := fresh "H" in
      assert (J := assoc g f A); rewrite J in I; clear J
    | context[(f ∘ (g ∘ ?B))] =>
      let J := fresh "H" in
      assert (J := assoc B g f); rewrite <- J in I; clear J
  end;
  match type of I with
    | context[f ∘ g] => idtac
    | _ => reveal_comp_in_I f g
  end
.
*)

Ltac simpl_ids :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J; clear J | trivial]
  in
  repeat(
      match goal with
        | [|- context[?A ∘ id] ] => rewrite id_unit_right
        | [|- context[id ∘ ?A] ] => rewrite id_unit_left
        | [|- ?A ∘ ?B = ?A] => id_detected B
        | [|- ?A = ?A ∘ ?B] => id_detected B
        | [|- ?B ∘ ?A = ?A] => id_detected B
        | [|- ?A = ?B ∘ ?A] => id_detected B
      end
    )
.

Ltac simpl_ids_in_I I :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J in I; clear J | trivial]
  in
  repeat(
      match type of I with
        | context[?A ∘ id] => rewrite id_unit_right in I
        | context[id ∘ ?A] => rewrite id_unit_left in I
        | ?A ∘ ?B = ?A => id_detected B
        | ?A = ?A ∘ ?B => id_detected B
        | ?B ∘ ?A = ?A => id_detected B
        | ?A = ?B ∘ ?A => id_detected B
      end
    )
.

Tactic Notation "simpl_ids" := simpl_ids.

Tactic Notation "simpl_ids" "in" hyp(I) := simpl_ids_in_I I.

Hint Extern 1 => progress simpl_ids.

Hint Extern 3 => progress (dohyps (fun H => simpl_ids in H)).

(* Automating use of functional_extensionality *)
Hint Extern 1 => 
match goal with
    [|- _ = _] =>
      let x := fresh "x" in
      extensionality x
end.

Hint Extern 3 =>
match goal with
    [|- ?A = ?B :> ?Hom _ _] =>
    repeat rewrite assoc; trivial; fail
end.


