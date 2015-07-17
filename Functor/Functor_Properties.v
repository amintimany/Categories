Require Import Category.Main.
Require Import Functor.Functor.
Require Import Functor.Functor_Ops.

Section Functor_Properties.
  Context {C C' : Category} (F : Functor C C').

  Local Open Scope object_scope.
  Local Open Scope morphism_scope.
    
  (** A functor is said to be injective if its object map is. *)
  Definition Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c = c'.

  (** A functor is said to be essentially injective if its object map maps
equal objects to isomorphic objects in the codomain category. *)
  Definition Essentially_Injective_Func := ∀ (c c' : Obj), F _o c = F _o c' → c ≡ c'.
  
  (** A functor is said to be surjective if its object map is. *)
  Definition Surjective_Func := ∀ (c : Obj), {c' : Obj | F _o c' = c}.

  (** A functor is said to be essentially surjective if for each object in the
codomain category there is an aobject in the domain category that is mapped
to an aobject isomorphic to it. *)
  Definition Essentially_Surjective_Func := ∀ (c : Obj), {c' : Obj & F _o c' ≡ c}.

  (** A functor is said to be faithful if its arrow map is injective. *)
  Definition Faithful_Func := ∀ (c c' : Obj) (h h' : Hom c c'), F _a h = F _a h' → h = h'.

  (** A functor is said to be full if its arrow map is surjective. *)
  Definition Full_Func := ∀ (c1 c2 : Obj) (h' : Hom (F _o c1) (F _o c2)),
      {h : Hom c1 c2 | F _a h = h'}
  .

  Local Ltac Inv_FTH :=
    match goal with
      [fl : Full_Func |- _] =>
      progress (
          repeat
            match goal with
              [|- context [(F _a (proj1_sig (fl _ _ ?x)))]] =>
              rewrite (proj2_sig (fl _ _ x))
            end
        )
    end
  .

  Local Hint Extern 1 => Inv_FTH.

  Local Hint Extern 1 => rewrite F_compose.

  Local Hint Extern 1 =>
  match goal with
    [fth : Faithful_Func |- _ = _ ] => apply fth
  end
  .

  Local Obligation Tactic := basic_simpl; auto 6.
  
  (** Any fully-faithful functor is essentially surjective. *)
  Program Definition Fully_Faithful_Essentially_Injective (fth : Faithful_Func) (fl : Full_Func)
    : Essentially_Injective_Func
    :=
      fun c c' eq =>
        {|
          iso_morphism :=
            proj1_sig (
                fl
                  _
                  _
                  match eq in _ = y return
                        Hom _ y
                  with
                    eq_refl => id (F _o c)
                  end
              );
          inverse_morphism :=
            proj1_sig (
                fl
                  _
                  _
                  match eq in _ = y return
                        Hom y _
                  with
                    eq_refl => id (F _o c)
                  end
              )
        |}
  .

  (** Any fully-faithful functor is conservative.

A conservative functor is one for which we have to objects of the domain category are isomorphic if their images are ismorphic. *)
  Program Definition Fully_Faithful_Conservative (fth : Faithful_Func) (fl : Full_Func)
    : ∀ (c c' : Obj), F _o c ≡ F _o c' → c ≡ c' :=
    fun c c' I =>
      {|
        iso_morphism := proj1_sig (fl _ _ I);
        inverse_morphism := proj1_sig (fl _ _ I⁻¹)
      |}
  .

End Functor_Properties.

(** Functors Preserve Isomorphisms. *)
Section Functors_Preserve_Isos.
  Context {C C' : Category} (F : Functor C C') {a b : C} (I : (a ≡≡ b ::> C)%morphism).

  Program Definition Functors_Preserve_Isos : (F _o a ≡ F _o b)%morphism :=
    {|
      iso_morphism := (F _a I)%morphism;
      inverse_morphism := (F _a I⁻¹)%morphism
    |}.

End Functors_Preserve_Isos.
  
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