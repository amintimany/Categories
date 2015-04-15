Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans.

Section Opposite_NatTrans.
  Context {C D : Category} {F F' : Functor C D} (N : NatTrans F F').

  Instance Opposite_NatTrans : NatTrans (Opposite_Functor F') (Opposite_Functor F) :=
    {
      Trans := Trans N;
      Trans_com := fun c c' h => (@Trans_com_sym _ _ _ _ N _ _ h);
      Trans_com_sym := fun c c' h => (@Trans_com _ _ _ _ N _ _ h)
    }.
  
End Opposite_NatTrans.

(* Composition of opposite nat transes *)

Section Compose_NOP.
  Context {C D : Category} {F F' F'' : Functor C D} (N : NatTrans F F') (N' : NatTrans F' F'').

  Theorem NatTrans_compose_Op : Opposite_NatTrans (NatTrans_compose N N') = NatTrans_compose (Opposite_NatTrans N') (Opposite_NatTrans N).
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End Compose_NOP.

(* Opposite of NatTrans_id *)

Section NatTrans_id_Op.
  Context {C D : Category} (F : Functor C D).

  Theorem NatTrans_id_Op : Opposite_NatTrans (NatTrans_id F) = NatTrans_id (Opposite_Functor F).
  Proof.
    apply NatTrans_eq_simplify.
    trivial.
  Qed.

End NatTrans_id_Op.

(* Horizontal composition of natural transformations *)

Program Instance NatTrans_hor_comp {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (tr : NatTrans F G) (tr' : NatTrans F' G') : NatTrans (Functor_compose F F') (Functor_compose G G') :=
{
  Trans := fun c : Obj => (G' _a _ _ (Trans tr c)) ∘ (Trans tr' (F _o c))
}.

Next Obligation. (* Trans_com*)
Proof.
  rewrite assoc.
  rewrite Trans_com.
  match goal with [|- ?A ∘ ?B ∘ ?C = ?D] => reveal_comp A B end.
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

Section Hor_Compose_ids.
  Context {C D E : Category} (F : Functor C D) (G : Functor D E).

  Theorem NatTrans_hor_comp_ids : (NatTrans_hor_comp (NatTrans_id F) (NatTrans_id G)) = NatTrans_id (Functor_compose F G).
  Proof.
    apply NatTrans_eq_simplify.
    cbn.
    extensionality c.
    rewrite F_id; simpl_ids; trivial.
  Qed.

End Hor_Compose_ids.

Section Hor_Compose_NOP.
  Context {C D E : Category} {F G : Functor C D} {F' G' : Functor D E} (N : NatTrans F G) (N' : NatTrans F' G').

  Theorem NatTrans_hor_comp_Op : Opposite_NatTrans (NatTrans_hor_comp N N') = NatTrans_hor_comp (Opposite_NatTrans N) (Opposite_NatTrans N').
  Proof.
    apply NatTrans_eq_simplify.
    simpl.
    extensionality c.
    rewrite Trans_com.
    trivial.
  Qed.

End Hor_Compose_NOP.

Program Instance NatTrans_to_compose_id {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose F (Functor_id _)) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_compose_id {C D : Category} (F : Functor C D) : NatTrans (Functor_compose F (Functor_id _)) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_to_id_compose {C D : Category} (F : Functor C D) : NatTrans F (Functor_compose (Functor_id _) F) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_from_id_compose {C D : Category} (F : Functor C D) : NatTrans (Functor_compose (Functor_id _) F) F :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose F (Functor_compose G H)) (Functor_compose (Functor_compose F G) H) :=
{
  Trans := fun c => id
}.

Program Instance NatTrans_Functor_assoc_sym {C1 C2 C3 C4 : Category}
        (F : Functor C1 C2)
        (G : Functor C2 C3)
        (H : Functor C3 C4)
: NatTrans (Functor_compose (Functor_compose F G) H) (Functor_compose F (Functor_compose G H)) :=
{
  Trans := fun c => id
}.

Section NatTrans_comp_hor_comp.
  Context {C D E  : Category} {F F' F'' : Functor C D} {G G' G'' : Functor D E} (N1 : NatTrans F F') (N2 : NatTrans G G') (N3 : NatTrans F' F'') (N4 : NatTrans G' G'').

  Theorem NatTrans_comp_hor_comp : NatTrans_compose (NatTrans_hor_comp N1 N2) (NatTrans_hor_comp N3 N4) = NatTrans_hor_comp (NatTrans_compose N1 N3) (NatTrans_compose N2 N4).
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c.
    cbn.
    rewrite F_compose.
    repeat rewrite assoc.
    match goal with
      [|- ?A ∘ ?B = ?A ∘ ?C] =>
      let H := fresh in
      cut (B = C); [intros H; rewrite H; trivial|]
    end.
    repeat rewrite assoc_sym.
    match goal with
      [|- ?A ∘ ?B = ?C ∘ ?B] =>
      let H := fresh in
      cut (A = C); [intros H; rewrite H; trivial|]
    end.
    apply Trans_com.
  Qed.    

End NatTrans_comp_hor_comp.