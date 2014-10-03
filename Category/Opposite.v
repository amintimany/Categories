Require Import Category.Category.
Require Import Category.Morph.

(* Oposite Category *)

Instance Opposite `(C : Category Obj Hom) : Category Obj (λ (a b : Obj), Hom b a) :=
{
  compose := λ a b c (f : Hom b a) (g : Hom c b), @compose _ _ C c b a g f;

  id := λ c, @id _ _ C c;
  
  assoc := λ _ _ _ _ f g h, @assoc_sym _ _ C _ _ _ _ h g f;

  assoc_sym := λ _ _ _ _ f g h, @assoc _ _ C _ _ _ _ h g f;

  id_unit_left := λ _ _ h, @id_unit_right _ _ C _ _ h;
  
  id_unit_right := λ _ _ h, @id_unit_left _ _ C _ _ h
                   
}.

(* Oposite defined *)

Notation "C '^op'" := (Opposite C) (at level 9, no associativity).

Theorem C_OP_OP `(C : Category Obj) : (C^op)^op = C.
Proof.
  destruct C; reflexivity.
Qed.

Hint Resolve C_OP_OP.

Definition C_OP_OP_sym `(C : Category Obj Hom) := eq_sym (@C_OP_OP _ _ C).

Hint Resolve C_OP_OP_sym.

Theorem CoIso `{C : Category Obj} (a b : Obj) : a ≡ b → @Isomorphic _ _ C^op a b. 
Proof.
  intros [f [g H1 H2]].
  exists g; exists f; auto.
Qed.