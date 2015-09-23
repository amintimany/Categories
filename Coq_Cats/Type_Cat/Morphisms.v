Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Require Import Coq.Logic.ChoiceFacts.

Local Axiom ConstructiveIndefiniteDescription_Type : forall T : Type, ConstructiveIndefiniteDescription_on T.

(** In this section we show that any morphism in Type_Cat (function
in Coq) can be split in to two morphisms where one is monic and the
other split epic. *)
Section split_Epic_Monic_Factorization.
  Context {A B : Type} (f : A → B).

  Definition Image_of : Type := {x : B | ∃ a, f a = x}.
  
  Definition From_Image_forward : Image_of → B := fun x => proj1_sig x.

  Program Definition Epic_Monic_Factor_Monic : @Monic Type_Cat Image_of B :=
    {|
      mono_morphism := From_Image_forward;
      mono_morphism_monomorphic := fun T g h => _
    |}
  .

  Next Obligation.
  Proof.
    extensionality x.
    assert (H' := equal_f H x); cbn in H'.
    apply sig_proof_irrelevance.
    destruct (g x); destruct (h x).
    trivial.
  Qed.
    
  Definition To_Image : A → Image_of :=
    fun a => exist _ (f a) (ex_intro _ a eq_refl).
  
  Definition From_Image_back : Image_of → A := fun x => proj1_sig (ConstructiveIndefiniteDescription_Type _ _ (proj2_sig x)).
  
  Theorem From_Image_back_form_split_epic : ∀ (x : Image_of), To_Image (From_Image_back x) = x.
  Proof.
    intros x.
    apply sig_proof_irrelevance.
    unfold From_Image_back; cbn.
    destruct
      (ConstructiveIndefiniteDescription_Type
         A
         (fun a : A => f a = proj1_sig x)
         (proj2_sig x)
      ) as [z Hz].
    trivial.
  Qed.

  Program Definition Epic_Monic_Factor_split_Epic : @is_split_Epic Type_Cat _ _ To_Image :=
    {|
      is_split_monic_left_inverse := From_Image_back
    |}.

  Next Obligation.
  Proof.
    extensionality x.
    apply From_Image_back_form_split_epic.
  Qed.

  Theorem split_Epic_Monic_Factorization :
    f = fun x =>  From_Image_forward (To_Image x).
  Proof.
    auto.
  Qed.    
    
End split_Epic_Monic_Factorization.
