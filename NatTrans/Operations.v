Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans.


(** The opposite of a natural transformation N : F -> F' is a nattrans N^op : F'^op -> F^op. It has the same arrow family as the original natural transformation. *)
Section Opposite_NatTrans.
  Context {C D : Category} {F F' : Functor C D} (N : NatTrans F F').

  Program Definition Opposite_NatTrans : NatTrans F'^op F^op :=
    {|
      Trans := Trans N;
      Trans_com := fun c c' h => (Trans_com_sym N h);
      Trans_com_sym := fun c c' h => (Trans_com N h)
    |}.
  
End Opposite_NatTrans.

Notation "N '^op'" := (Opposite_NatTrans N) (at level 9, no associativity) : nattrans_scope.

(** Composition of opposite natural transformations is just the same as the opposite natural transformation of the composition. *)
Section Compose_NOP.
  Context {C D : Category} {F F' F'' : Functor C D} (N : NatTrans F F') (N' : NatTrans F' F'').

  Theorem NatTrans_compose_Op : ((N' ∘ N)^op = N^op ∘ N'^op)%nattrans.
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End Compose_NOP.

(** Opposite of NatTrans_id is just NatTrans_id of the opposite functor *)
Section NatTrans_id_Op.
  Context {C D : Category} (F : Functor C D).

  Theorem NatTrans_id_Op : ((NatTrans_id F)^op)%nattrans = NatTrans_id (F^op)%functor.
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End NatTrans_id_Op.

(** Horizontal composition of natural transformations:

Let C, D and E be categories, F: C -> D G : C -> D, F' : D -> E and G' : D -> E be functors and N : F -> G and N' : F' -> G' be natural transformations. Then, the horizontal composition of N and N', denoted by N ∘_h N' : F' ∘ F -> G' ∘ G is defined as follows:

 *)
Program Definition NatTrans_hor_comp {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (tr : NatTrans F G) (tr' : NatTrans F' G') : NatTrans (F' ∘ F) (G' ∘ G) :=
{|
  Trans := fun c : Obj => ((G' _a (Trans tr c)) ∘ (Trans tr' (F _o c)))%morphism
|}.

Next Obligation. (* Trans_com*)
Proof.
  rewrite assoc.
  rewrite Trans_com.
  rewrite assoc_sym.
  rewrite <- F_compose.
  rewrite Trans_com.
  rewrite F_compose.
  auto.
Qed.

Next Obligation. (* Trans_com*)
Proof.
  symmetry.
  apply NatTrans_hor_comp_obligation_1.
Qed.

(**
Graphically:
#
<pre>
    C      C             C              C       
    |  N   |             |              |
  F | ===> | G           |              |
    |      |             |              |
    ∨      ∨             |   N' ∘_h N   |
    D      D        F'∘F | ===========> |
    |  N'  |             |              |
 F' | ===> | G'          |              |
    |      |             |              |
    ∨      ∨             ∨              ∨
    E      E             E              E
</pre>
#
*)

Notation "N ∘_h N'" := (NatTrans_hor_comp N' N) : nattrans_scope.

(** Horizontal composition of NatTrans_ids is just the NatTrans_id of the composition of underlying functors. *)
Section Hor_Compose_ids.
  Context {C D E : Category} (F : Functor C D) (G : Functor D E).

  Theorem NatTrans_hor_comp_ids : ((NatTrans_id G) ∘_h (NatTrans_id F))%nattrans = NatTrans_id  (G ∘ F).
  Proof.
    apply NatTrans_eq_simplify.
    cbn.
    extensionality c.
    rewrite F_id; simpl_ids; trivial.
  Qed.

End Hor_Compose_ids.

(** Horizontal composition of opposite of two natural transformations is just the opposite of the horizontal composition of those two natural transformations. *)
Section Hor_Compose_NOP.
  Context {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (N : NatTrans F G) (N' : NatTrans F' G').
  
  Theorem NatTrans_hor_comp_Op : ((N' ∘_h N)^op = N'^op ∘_h N^op)%nattrans.
  Proof.
    apply NatTrans_eq_simplify.
    cbn.
    extensionality c.
    rewrite Trans_com.
    trivial.
  Qed.

End Hor_Compose_NOP.

(** Natural transformation from a functor to itself composed with id on the right. *)
Program Definition NatTrans_to_compose_id {C D : Category} (F : Functor C D) : NatTrans F ((Functor_id D) ∘ F) :=
{|
  Trans := fun c => id
|}.

(** Natural transformation to a functor from itself composed with id on the right. *)
Program Definition NatTrans_from_compose_id {C D : Category} (F : Functor C D) : NatTrans ((Functor_id _) ∘ F) F :=
{|
  Trans := fun c => id
|}.

(** Natural transformation from a functor to itself composed with id on the left. *)
Program Definition NatTrans_to_id_compose {C D : Category} (F : Functor C D) : NatTrans F (F ∘ (Functor_id _)) :=
{|
  Trans := fun c => id
|}.

(** Natural transformation to a functor from itself composed with id on the left. *)
Program Definition NatTrans_from_id_compose {C D : Category} (F : Functor C D) : NatTrans (F ∘ (Functor_id _)) F :=
{|
  Trans := fun c => id
|}.

(** Natural transformation corresponding to associativity of functor composition *)
Program Definition NatTrans_Functor_assoc {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans ((H ∘ G) ∘ F) (H ∘ (G ∘ F)) :=
{|
  Trans := fun c => id
|}.

(** Natural transformation corresponding to the symmetric form of associativity of functor composition *)
Program Definition NatTrans_Functor_assoc_sym {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (H ∘ (G ∘ F)) ((H ∘ G) ∘ F) :=
{|
  Trans := fun c => id
|}.

(**
The following theorem states that the two natural transformations of the diagram in the middle are equal.
#
<pre>
    F                       G ∘ F                      G
 C —————––>D   D —————————–—————————————————–—–—–> E   D —–————–> E
     ||           ||                           ||          ||
     ||N1         ||                           ||          ||N2
     ||           ||                           ||          ||
     \/           ||                           ||          \/
     F'           ||                           ||          G'
 C ————–—–>D      ||(N4 ∘ N2) ∘_h (N3 ∘ N1)    ||      D ———–——–> E
     ||           ||                           ||          ||
     || N3        ||                           ||          ||N4
     ||           ||  (N4 ∘_h N3) ∘ (N2 ∘_h N1)||          ||
     \/           ||                           ||          \/
     F''          \/                           \/          G''
 C ————–—–> D  D ——–—————————————————————————–——–> E   D————–——–> E
                            G'' ∘ F''
</pre>
#
*)
Section NatTrans_comp_hor_comp.
  Context {C D E  : Category} {F F' F'' : Functor C D} {G G' G'' : Functor D E} (N1 : NatTrans F F') (N2 : NatTrans G G') (N3 : NatTrans F' F'') (N4 : NatTrans G' G'').

  Theorem NatTrans_comp_hor_comp : ((N4 ∘_h N3) ∘ (N2 ∘_h N1) = (N4 ∘ N2) ∘_h (N3 ∘ N1))%nattrans.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c.
    cbn.
    rewrite F_compose.
    repeat rewrite assoc.
    match goal with
      [|- (?A ∘ ?B = ?A ∘ ?C)%morphism] =>
      let H := fresh in
      cut (B = C); [intros H; rewrite H; trivial|]
    end.
    repeat rewrite assoc_sym.
    match goal with
      [|- (?A ∘ ?B = ?C ∘ ?B)%morphism] =>
      let H := fresh in
      cut (A = C); [intros H; rewrite H; trivial|]
    end.
    apply Trans_com.
  Qed.    

End NatTrans_comp_hor_comp.

(**
Given I : C ≡≡ D for categories C and D and F : D -> E, there is a natural transformation
from F ∘ (I ∘ I⁻¹) to F and back.
*)
Section IsoCat_NatTrans.
  Context {C D : Category} (I : (C ≡≡ D ::> Cat)%morphism) {E : Category} (F : Functor D E).

  Local Obligation Tactic := idtac.
  
  Program Definition IsoCat_NatTrans :
    NatTrans (F ∘ ((iso_morphism I) ∘ (I⁻¹)%morphism)) F
    :=
      {|
        Trans :=
          fun c =>
            match eq_sym (f_equal (fun x => (x _o)%object c) (right_inverse I)) in _ = y return
                  Hom (F _o y) (F _o c)
            with
              eq_refl => id
            end
      |}
  .

  Next Obligation.
  Proof.
    intros c c' h; cbn.
    match goal with
      [|- (match ?e with _ => _ end ∘ ?A)%morphism = (?B ∘ match ?e' with _ => _ end)%morphism] =>
      generalize e; generalize e';
      set (U := A); set (V := B)
    end.
    intros H H'.
    cut (JMeq U V); [intros HUV|].
    {
      apply JMeq_eq.
      destruct H.
      set (z' := ((iso_morphism I) _o ((inverse_morphism I) _o c'))%object) in *.
      clearbody U.
      clearbody z'.
      destruct H'.
      auto.
    }
    {
      unfold U, V; clear.
      match goal with
        [|- JMeq (F @_a ?A ?B ?C)%morphism (F _a ?D)%morphism] =>
        set (V := C);
        set (M := A) in *;
        set (N := B) in *;
        set (U := D)
      end.
      cut (M = c); [intros Hc|].
      {
        cut (N = c'); [intros Hc'|].
        {
          cut (JMeq V U); [intros HVU|].
          {
            clearbody U V M N.
            destruct Hc.
            destruct Hc'.
            apply JMeq_eq in HVU.
            destruct HVU.
            trivial.
          }
          {
            unfold U, V, M, N; clear.
            change ((iso_morphism I) _o ((I⁻¹)%morphism _o c))%object
            with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c)%object.
            change ((iso_morphism I) _o ((I⁻¹)%morphism _o c'))%object
            with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c')%object.
            change ((iso_morphism I) _a (I⁻¹ _a h))%morphism with (((iso_morphism I) ∘ I⁻¹) _a h)%morphism.
            cbn_rewrite (right_inverse I).
            trivial.            
          }
        }
        {
          unfold N; clear.
          change ((iso_morphism I) _o ((I⁻¹)%morphism _o c'))%object
          with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c')%object.        
          cbn_rewrite (right_inverse I); trivial.
        }
      }
      {
        unfold M; clear.
        change ((iso_morphism I) _o ((I⁻¹)%morphism _o c))%object
        with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c)%object.        
        cbn_rewrite (right_inverse I); trivial.
      }
    }
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply IsoCat_NatTrans_obligation_1.
  Qed.

  Program Definition IsoCat_NatTrans_back :
    NatTrans F (F ∘ ((iso_morphism I) ∘ (I⁻¹)%morphism))
    :=
      {|
        Trans :=
          fun c =>
            match eq_sym (f_equal (fun x => (x _o)%object c) (right_inverse I)) in _ = y return
                  Hom (F _o c) (F _o y)
            with
              eq_refl => id
            end
      |}
  .
    
  Next Obligation.
  Proof.
    intros c c' h; cbn.
    match goal with
      [|- (match ?e with _ => _ end ∘ ?A)%morphism = (?B ∘ match ?e' with _ => _ end)%morphism] =>
      generalize e; generalize e';
      set (U := A); set (V := B)
    end.
    intros H H'.
    cut (JMeq U V); [intros HUV|].
    {
      apply JMeq_eq.
      destruct H'.
      set (z := ((iso_morphism I) _o ((inverse_morphism I) _o c))%object) in *.
      clearbody V.
      clearbody z.
      destruct H.
      auto.
    }
    {
      unfold U, V; clear.
      match goal with
        [|- JMeq (F _a ?D)%morphism (F @_a ?A ?B ?C)%morphism] =>
        set (V := C);
        set (M := A) in *;
        set (N := B) in *;
        set (U := D)
      end.
      cut (M = c); [intros Hc|].
      {
        cut (N = c'); [intros Hc'|].
        {
          cut (JMeq U V); [intros HUV|].
          {
            clearbody U V M N.
            destruct Hc.
            destruct Hc'.
            apply JMeq_eq in HUV.
            destruct HUV.
            trivial.
          }
          {
            unfold U, V, M, N; clear.
            change ((iso_morphism I) _o ((I⁻¹)%morphism _o c))%object
            with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c)%object.
            change ((iso_morphism I) _o ((I⁻¹)%morphism _o c'))%object
            with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c')%object.
            change ((iso_morphism I) _a (I⁻¹ _a h))%morphism with (((iso_morphism I) ∘ I⁻¹) _a h)%morphism.
            cbn_rewrite (right_inverse I).
            trivial.            
          }
        }
        {
          unfold N; clear.
          change ((iso_morphism I) _o ((I⁻¹)%morphism _o c'))%object
          with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c')%object.        
          cbn_rewrite (right_inverse I); trivial.
        }
      }
      {
        unfold M; clear.
        change ((iso_morphism I) _o ((I⁻¹)%morphism _o c))%object
        with (((iso_morphism I) ∘ (I⁻¹)%morphism) _o c)%object.        
        cbn_rewrite (right_inverse I); trivial.
      }
    }
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply IsoCat_NatTrans_back_obligation_1.
  Qed.

End IsoCat_NatTrans.