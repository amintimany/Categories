Require Import Category.Category.
Require Import Ext_Cons.Arrow.
Require Import Functor.Functor Functor.Functor_Ops Const_Func.
Require Import Archetypal.Discr.

Section Comma.
  Context {B C D : Category} (F : Functor B C) (G : Functor D C).

  Class Comma_Obj : Type :=
    {
      CMO_src : B;
      CMO_trg : D;
      CMO_hom : Hom (F _o CMO_src) (G _o CMO_trg)
    }.

  Class Comma_Hom (a b : Comma_Obj) : Type :=
    {
      CMH_left : Hom (@CMO_src a) (@CMO_src b);
      CMH_right : Hom (@CMO_trg a) (@CMO_trg b);
      CMH_com :  (G _a _ _ CMH_right) ∘ (@CMO_hom a) = (@CMO_hom b) ∘ (F _a _ _ CMH_left)
    }.

  Theorem Comma_Hom_eq_simplify {a b : Comma_Obj} (h h' : Comma_Hom a b) : (@CMH_left _ _ h) = (@CMH_left _ _ h') → (@CMH_right _ _ h) = (@CMH_right _ _ h') → h = h'.
  Proof.
    intros H1 H2.
    destruct h as [hl hr hc]; destruct h' as [hl' hr' hc'].
    cbn in *.
    destruct H1; destruct H2.
    destruct (proof_irrelevance _ hc hc').
    trivial.
  Qed.

  Program Instance Comma_Hom_compose {a b c : Comma_Obj} (h : Comma_Hom a b) (h' : Comma_Hom b c) : Comma_Hom a c :=
    {
      CMH_left := (@CMH_left _ _ h') ∘ (@CMH_left _ _ h);
      CMH_right := (@CMH_right _ _ h') ∘ (@CMH_right _ _ h)
    }.

  Next Obligation.
  Proof.
    repeat rewrite F_compose.
    rewrite assoc.
    rewrite CMH_com.
    rewrite assoc_sym.
    rewrite CMH_com.
    auto.
  Qed.

  Theorem Comma_Hom_compose_assoc {a b c d : Comma_Obj} (h : Comma_Hom a b) (h' : Comma_Hom b c) (h'' : Comma_Hom c d) : Comma_Hom_compose h (Comma_Hom_compose h' h'') = Comma_Hom_compose (Comma_Hom_compose h h') h''.
  Proof.                    
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.    

  Program Instance Comma_Hom_id (a : Comma_Obj) : Comma_Hom a a :=
    {
      CMH_left := id;
      CMH_right := id
    }.

  Theorem Comma_Hom_id_unit_left {a b : Comma_Obj} (h : Comma_Hom a b) : Comma_Hom_compose h (Comma_Hom_id b) = h.
  Proof.
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.

  Theorem Comma_Hom_id_unit_right {a b : Comma_Obj} (h : Comma_Hom a b) : Comma_Hom_compose (Comma_Hom_id a) h = h.
  Proof.
    apply Comma_Hom_eq_simplify; cbn; auto.
  Qed.

  
  Program Instance Comma : Category :=
    {
      Obj := Comma_Obj;

      Hom := Comma_Hom;

      compose := @Comma_Hom_compose;

      assoc := @Comma_Hom_compose_assoc;

      assoc_sym := fun _ _ _ _ f g h => eq_sym (Comma_Hom_compose_assoc f g h);
      
      id := Comma_Hom_id;

      id_unit_right := @Comma_Hom_id_unit_right;

      id_unit_left := @Comma_Hom_id_unit_left
    }.

End Comma.

Arguments CMO_src {_ _ _ _ _} _.
Arguments CMO_trg {_ _ _ _ _} _.
Arguments CMO_hom {_ _ _ _ _} _.
Arguments CMH_left {_ _ _ _ _ _ _} _.
Arguments CMH_right {_ _ _ _ _ _ _} _.
Arguments CMH_com {_ _ _ _ _ _ _} _.

Section Slice_CoSlice.
  Context (C : Category) (c : Obj).
  
  (*
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, an arrow from g to h is a pair of arrows f : a → b s.t. the ollowing commutes:

           g
         a –––→ c
         |     ↗
         ∣    /    
        f∣   / h
         |  /
         ↓ /
         b 

   *)

  Instance Slice : Category := Comma (Functor_id _) (Const_Func 1 c).

  (*
   The Slice of Category C with respect to c:
     Objects : Arrows of C ending in c
     Arrows: for g : a → c and h : b → c, an arrow from g to h is a pair of arrows f : a → b s.t. the ollowing commutes:

            g
         c ←––– a
         ↑     /
         ∣    /
        h∣   / f
         |  /
         | ↙
         b 

   *)

  Instance CoSlice : Category := Comma (Const_Func 1 c) (Functor_id _).

End Slice_CoSlice.

Section Arrow_Cat.
  Context (C : Category).

  (*
   The Arrow Category of C:
     Objects : Arrows of C
     Arrows: for g : a → b and h : c → d, an arrow from g to h is a pair of arrows (f,f') s.t. the ollowing commutes:

             g
         a ––––→ b
         ∣       ∣
        f∣       ∣f'
         ↓       ↓
         c –——–→ d
             h
   *)

  Instance Arrow_Cat : Category := Comma (Functor_id C) (Functor_id C).

End Arrow_Cat.


