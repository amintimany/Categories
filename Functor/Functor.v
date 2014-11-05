Require Import Category.Main.

Set Primitive Projections.

Set Universe Polymorphism.

Class Functor (C C' : Category) : Type := 
{
  (* Object map *)
  FO : @Obj C → @Obj C';

  (* Arrow map *)
  FA : ∀ {a b}, @Hom C a b → @Hom C' (FO a) (FO b);

  (* Mapping of identities *)
  F_id : ∀ {c}, FA (@id _ c) = @id _ (FO c);
  
  (* Functor commuting with composition *)
  F_compose : ∀ {a b c} (f : Hom a b) (g : Hom b c), FA (g ∘ f) = (FA g) ∘ (FA f)

  (* F_id and F_compose together state the fact that functors are morphisms of categories (preserving the structure of categories!)*)
}.

Notation "F '_o'" := (@FO _ _ F).

Notation "F '_a'" := (@FA _ _ F).

Hint Extern 2 => (apply F_id).

Ltac Functor_Simplify :=
  match goal with
    | [|- ?F _a _ _ ?A = @id _ _ _ (?F _o ?x)] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- (@id _ _ _ (?F _o ?x)) = ?F _a _ _ ?A] =>
      rewrite <- F_id; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C ∘ ?F _a _ _ ?D] =>
      repeat rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?A ∘ ?F _a _ _ ?B = ?F _a _ _ ?C] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- ?F _a _ _ ?C = ?F _a _ _ ?A ∘ ?F _a _ _ ?B] =>
      rewrite <- F_compose; (simpl||idtac)
    | [|- context [?F _a _ _ id] ] =>
      rewrite F_id; (simpl||idtac)
    | [|- context [?F _a _ _ ?A ∘ ?F _a _ _ ?B]] =>
      rewrite <- F_compose; (simpl||idtac)
  end
.

Hint Extern 2 => Functor_Simplify.

Section Functor_eq_simplification.

  Context {C C' : Category} (F G : Functor C C').

  Lemma Functor_eq_simplify : (F _o = G _o) -> (F _a ≃ G  _a) -> F = G.
  Proof.
    intros H1 H2.
    destruct F as [fO fA fid fco]; destruct G as [gO gA gid gco]; simpl in *.
    destruct H1.
    dependent destruction H2.
    destruct (proof_irrelevance _ fid gid).
    destruct (proof_irrelevance _ fco gco).
    reflexivity.
  Qed.

  Theorem FA_extensionality : (F _o = G _o) → (∀ (a b : Obj) (h : Hom a b), F _a _ _ h ≃ G _a _ _ h) → F _a ≃ G _a.
  Proof.
    intros Oeq H.
    destruct F as [fO fA f_id f_cmp]; destruct G as [gO gA g_id g_cmp]; simpl in *.
    eapply (@JMeq_trans _ _ _ _ (
                          fun (a b : Obj) (f : Hom a b) =>
                            match 
                              (match 
                                  (match Oeq in (_ = u) return (fO a = u a) with
                                       eq_refl => eq_refl
                                   end)
                                  in (_ = Y) return (Hom (fO a) _ = Hom Y _) with
                                    eq_refl => 
                                    (match
                                        (match Oeq in (_ = u) return (fO b = u b) with
                                             eq_refl => eq_refl
                                         end)
                                        in (_ = Y) return (Hom _ (fO b) = Hom _ Y) with
                                          eq_refl => eq_refl
                                      end)
                                end) in (_ = Z) return Z with
                                eq_refl => fA _ _ f
                            end
                        ) _).
    {
      destruct Oeq; trivial.
    }
    {
      match goal with
          [|- ?A ~= ?B] => let H := fresh "H" in cutrewrite(A = B); trivial
      end.
      extensionality x; extensionality y; extensionality f.
      match goal with
          [|- ?A = ?B] => let H := fresh "H" in cut(A ~= B); [intros H; rewrite H; trivial|]
      end.
      rewrite <- (H x y f).
      destruct Oeq; trivial.
    }
  Qed.

  Lemma Functor_extensionality : (∀ (x : Obj), F _o x = G _o x) -> (∀ (a b : Obj) (h : Hom a b), F _a _ _ h ~= G _a _ _ h) → F = G.
  Proof.
    intros H H'.
    apply Functor_eq_simplify; trivial.
    extensionality x; trivial.
    apply FA_extensionality; trivial.
    extensionality x; trivial.
  Qed.

End Functor_eq_simplification.

Section FA_equal_f.
  Context {A : Type} {A' : Type}
          {B : A → A → Type} {B' : A' → A' → Type}
          {FO GO : A -> A'}
          (FA : ∀ (a b : A), B a b → B' (FO a) (FO b))
          (GA : ∀ (a b : A),  B a b → B' (GO a) (GO b))
  .

Lemma FA_equal_f : FO = GO -> FA ≃ GA → ∀ (a b : A) (f : B a b), FA _ _ f ≃ GA _ _ f.
Proof.
  intros H1 H2 a b f.
  symmetry in H1.
  apply (fun P => @JMeq_trans _ _ _ P
  (
    match H1 in (_ = Y) return B' (Y a) (Y b) with
        eq_refl => GA a b f
    end
  ) _).
  dependent destruction H1.
  dependent destruction H2.
  reflexivity.
  destruct H1; reflexivity.
Qed.

End FA_equal_f.