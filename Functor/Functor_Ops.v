From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.

(**
Opposite of a functor F : C -> D is a functor F^op : C^op -> D^op with the same
object and arrow maps.
 *)
Section Opposite_Functor.
  Context {C D : category} (F : functor C D).

  Local Open Scope morphism_scope.
  Local Open Scope object_scope.

  Program Definition opposite_functor : functor (C ᴼᴾ) (D ᴼᴾ) :=
    {|
      FO := F ₒ;
      FA := fun _ _ h => F @ₐ _ _ h;
      F_id := fun a => F_id F a;
      F_compose := fun _ _ _ f g => F_compose F g f
    |}.

End Opposite_Functor.

Notation "F 'ᴼᴾ'" := (opposite_functor F) : functor_scope.

(* We can compose functors. The object and arrow maps are simply function
   compositions of object and arrow maps. *)
Program Definition functor_compose {C C' C'' : category} (F : functor C C') (F' : functor C' C'') : functor C C'' :=
  {|
    FO := fun c => (F' ₒ (F ₒ c))%object;
    FA := fun c d f => (F' ₐ (F ₐ f))%morphism
  |}.
  Solve All Obligations with simpl; auto.
  Fail Next Obligation.

Notation "F ∘ G" := (functor_compose G F) : functor_scope. 

(** Associativity of functor composition *)
Theorem Functor_assoc {C1 C2 C3 C4} (F : functor C1 C2) (G : functor C2 C3) (H : functor C3 C4) :
  ((H ∘ G) ∘ F = H ∘ (G ∘ F))%functor.
Proof.  Func_eq_simpl; done. Qed.

(** The identitiy functor *)

Program Definition functor_id (C : category) : functor C C :=
  {|
    FO := fun x => x;
    FA := fun c d f => f
  |}.
Solve All Obligations with simpl; auto.
Fail Next Obligation.

(** Fucntor_id is the left ididntity of functor composition. *)
Theorem Functor_id_unit_left (C C' : category) (F : functor C C') : ((functor_id C') ∘ F)%functor = F.
Proof. Func_eq_simpl; trivial. Qed.

(** Functor_id is the right identity of functor composition. *)
Theorem Functor_id_unit_right (C C' : category) (F : functor C C') : (functor_compose (functor_id _) F) = F.
Proof. Func_eq_simpl; trivial. Qed.
