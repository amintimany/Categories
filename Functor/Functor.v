From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

(**
Fro categories C and C', a functor F : C -> C' consists of an arrow map from
objects of C to objects of C' and an arrow map from arrows of C to arrows of C'
such that an arrow h : a -> b is mapped to (F h) : F a -> F b.

Furthermore, we require functors to map identitiies to identities. Additionally,
the immage of the coposition of two arrows must be the same as composition of
their images.
*)
Record functor (C C' : category) : Type :=
{
  (** Object map *)
  FO : C → C';

  (** Arrow map *)
  FA : ∀ {a b}, hom a b → hom (FO a) (FO b);

  (** Mapping of identities *)
  F_id : ∀ c, FA (id c) = id (FO c);

  (** Functor commuting with composition *)
  F_compose : ∀ {a b c} (f : hom a b) (g : hom b c), (FA (g ∘ f) = (FA g) ∘ (FA f))%morphism

  (* F_id and F_compose together state the fact that functors are morphisms of
 categories (preserving the structure of categories!)*)
}.

Arguments FO {_ _} _ _.
Arguments FA {_ _} _ _ _ _.
Arguments F_id {_ _} _ _.
Arguments F_compose {_ _} _ {_ _ _} _ _.

Bind Scope functor_scope with functor.

Notation "F 'ₒ'" := (FO F) : object_scope.

Notation "F '@ₐ'" := (@FA _ _ F) : morphism_scope.

Notation "F 'ₐ'" := (@FA _ _ F _ _) : morphism_scope.

Hint Extern 2 => (apply F_id) : core.

Ltac Functor_Simplify :=
  progress
    (
      repeat rewrite F_id;
      (
        repeat
          match goal with
          | [|- (?F ₐ ?A)%morphism = id (?F ₒ ?x)] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- (id (?F ₒ ?x)) = (?F ₐ ?A)%morphism] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- (?F ₐ ?A ∘ ?F ₐ ?B = ?F ₐ ?C ∘ ?F ₐ ?D)%morphism] =>
            (repeat rewrite <- F_compose; (cbn+idtac))
          | [|- (?F ₐ ?A ∘ ?F ₐ ?B = ?F ₐ ?C)%morphism] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- (?F ₐ ?C = ?F ₐ ?A ∘ ?F ₐ ?B)%morphism] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- context [(?F ₐ ?A ∘ ?F ₐ ?B)%morphism]] =>
            (rewrite <- F_compose; (cbn+idtac))
          end
      )
    )
.

Hint Extern 2 => Functor_Simplify : core.

(** Two functors are equal if their object maps and arrow maps are. *)
Lemma Functor_eq_simplify {C C' : category} (F G : functor C C') (oeq : ∀ c, (F ₒ c = G ₒ c)%object) :
  (∀ c c' h, (hom_trans (oeq c) (oeq c') (F ₐ h)) = G ₐ h)%morphism -> F = G.
Proof.
  destruct F as [Fo Fh]; destruct G as [Go Gh]; intros heq; simpl in *.
  assert (Fo = Go) as oeq' by by extensionality c; rewrite oeq.
  ElimEq.
  assert (Fh = Gh).
  { extensionality c; extensionality d; extensionality h; rewrite -heq hom_trans_refl //. }
  ElimEq.
  PIR; done.
Qed.

Hint Extern 2 => Functor_Simplify : core.

Ltac Func_eq_simpl :=
  match goal with
    [|- ?A = ?B :> functor _ _] =>
    (apply (Functor_eq_simplify A B (λ x, eq_refl (A ₒ x) : A ₒ x = B ₒ x)%object)) +
    (cut (∀ x, A ₒ x = B ₒ x)%object; [
       let u := fresh "H" in
       intros u;
         apply (Functor_eq_simplify A B u)
         |
    ])
  end.

Hint Extern 3 => Func_eq_simpl : core.

Lemma Functor_eq_morph [C C' : category] [F G : functor C C'] (FGeq : F = G) [x y] (h : hom x y) :
  (hom_trans (equal_f (f_equal FO FGeq) x) (equal_f (f_equal FO FGeq) y) (F ₐ h) = G ₐ h)%morphism.
Proof. destruct FGeq; trivial. Qed.
