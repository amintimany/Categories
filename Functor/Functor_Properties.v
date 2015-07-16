Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Functor_Ops.

Section Functor_Properties.
  Context {C C' : Category} (F : Functor C C').

  Local Open Scope object_scope.
  Local Open Scope morphism_scope.
    
  (** A functor is said to be injective if its object map is. *)
  Definition Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c = c'.

  (** A functor is said to be essentially injective if its object map maps equal objects to isomorphic objects in the codomain category. *)
  Definition Essentially_Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c ≡ c'.
  
  (** A functor is said to be surjective if its object map is. *)
  Definition Surjective_Func := ∀ (c : Obj), {c' : Obj | F _o c' = c}.

  (** A functor is said to be essentially surjective if for each object in the codomain category there is an aobject in the domain category that is mapped to an aobject isomorphic to it. *)
  Definition Essentially_Surjective_Func := ∀ (c : Obj), {c' : Obj & F _o c' ≡ c}.

  (** A functor is said to be faithful if its arrow map is injective. *)
  Definition Faithful_Func := ∀ (c c' : Obj) (h h' : Hom c c'), F _a h = F _a h' → h = h'.

  (** A functor is said to be full if its arrow map is surjective. *)
  Definition Full_Func := ∀ (c1 c2 : Obj) (h' : Hom (F _o c1) (F _o c2)), {h : Hom c1 c2 | F _a h = h'}.

  (** Any fully-faithful functor is essentially surjective. *)
  Theorem Fully_Faithful_Essentially_Injective : Faithful_Func → Full_Func → Essentially_Injective_Func.
  Proof.
    intros F_Faithful F_Full c c' H.
    destruct (F_Full _ _ (
                       match H in (_ = Y) return Hom (F _o c) Y with
                         | eq_refl => F _a (id c)
                       end)
             ) as [U' HU].
    destruct (F_Full _ _ (
                       match H in (_ = Y) return Hom Y (F _o c) with
                         | eq_refl => F _a (id c)
                       end)
             ) as [V' HV].
    apply (Build_Isomorphism _ _ _ U' V');
      apply F_Faithful; rewrite F_compose;
      rewrite HU, HV;
      repeat rewrite F_id; clear; destruct H; auto.
  Qed.

  (** Any fully-faithful functor is conservative.

A conservative functor is one for which we have to objects of the domain category are isomorphic if their images are ismorphic. *)
  Theorem Fully_Faithful_Conservative : Faithful_Func → Full_Func → ∀ (c c' : Obj), F _o c ≡ F _o c' → c ≡ c'.
  Proof.
    intros F_Faithful F_Full c c' [f g H1 H2].
    destruct (F_Full _ _ f) as [Ff Hf].
    destruct (F_Full _ _ g) as [Fg Hg].
    apply (Build_Isomorphism _ _ _ Ff Fg);
      apply F_Faithful;
      rewrite F_compose;
      rewrite Hf, Hg, F_id; trivial.
  Qed.

End Functor_Properties.

Section Embedding.
  Context (C C' : Category).

  (**
    An embedding is a functor that is faully-faithful. Such a functor is necessarily essentially injective and conservative, i.e., if F _O c ≡ F _O c' then c ≡ c'.
   *)

  Record Embedding : Type :=
    {
      Emb_Func : Functor C C';

      Emb_Faithful : Faithful_Func Emb_Func;
      
      Emb_Full : Full_Func Emb_Func
    }.

  Coercion Emb_Func : Embedding >-> Functor.

  Definition Emb_Essent_Inj (E : Embedding) := Fully_Faithful_Essentially_Injective (Emb_Func E) (Emb_Faithful E) (Emb_Full E).
  
  Definition Emb_Conservative (E : Embedding) := Fully_Faithful_Conservative (Emb_Func E) (Emb_Faithful E) (Emb_Full E).

End Embedding.

Arguments Emb_Func {_ _} _.
Arguments Emb_Faithful {_ _} _ {_ _} _ _ _.
Arguments Emb_Full {_ _} _ {_ _} _.
