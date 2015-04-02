Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.
Require Import Functor.Main.
Require Import Functor.Representable.Hom_Func Functor.Representable.Hom_Func_Prop.
Require Import NatTrans.NatTrans.
Require Import Adjunction.Adjunction.

Section Hom_Adj_Duality.
  Context {C D : Category} (F : Functor C D) (G : Functor D C) (adj : Hom_Adjunct F G).
  
  Instance Hom_Adjunct_Duality : Hom_Adjunct (Opposite_Functor G) (Opposite_Functor F).
  Proof.
    set (V := NatIso_hor_comp (NatTrans_id_Iso (Twist_Func D C^op)) adj).
    unfold Hom_Adjunct.
    set (HC := (Hom_Func_Twist C^op) : Hom_Func C = Functor_compose (Twist_Func C ^op C) (Hom_Func C ^op)); rewrite HC in V; clear HC.
    set (HD := (Hom_Func_Twist D^op) : Hom_Func D = Functor_compose (Twist_Func D ^op D) (Hom_Func D ^op)); rewrite HD in V; clear HD.
    rewrite (Functor_assoc _ _ (Hom_Func D ^op)) in V.
    rewrite (Functor_assoc (Twist_Func D C^op) _ _) in V.
    change (Opposite (Opposite C)) with C in V.
    change (Opposite (Opposite D)) with D in V.
    rewrite Twist_Prod_Func_Twist in V.
    rewrite (Functor_assoc _ _ (Hom_Func C ^op)) in V.
    rewrite (Functor_assoc (Twist_Func D C^op) _ _) in V.
    change (Opposite (Opposite C)) with C in V.
    change (Opposite (Opposite D)) with D in V.
    rewrite Twist_Prod_Func_Twist in V.
    apply Inverse_Isomorphism in V.
    exact V.
  Qed. (* if changed to Defined, makes the compile time VERY long. ~ 27 seconds! *)

End Hom_Adj_Duality.

Section Adj_Duality.
  Context {C D : Category} (F : Functor C D) (G : Functor D C) (adj : Adjunct F G).
  
  Instance Adjunct_Duality : Adjunct (Opposite_Functor G) (Opposite_Functor F).
  Proof.
    apply Adj_to_Hom_Adj in adj.
    apply Hom_Adjunct_Duality in adj.
    apply Hom_Adj_to_Adj in adj.
    exact adj.
  Defined.

End Adj_Duality.