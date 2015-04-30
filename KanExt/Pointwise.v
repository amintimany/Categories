Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops Functor.Representable.Hom_Func Functor.Representable.Representable.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat.
Require Import KanExt.Local.


Local Notation FCOMP := Functor_compose (only parsing).
Local Notation FOP := Opposite_Functor (only parsing).
Local Notation NCOMP := NatTrans_compose (only parsing).
Local Notation HCOMP := NatTrans_hor_comp (only parsing).
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Section Pointwise_LRKE.
  Context {C C' : Category} {p : Functor C C'} {D: Category} {F : Functor C D} (lrke : Local_Right_KanExt p F).

  Definition Pointwise_LRKE := ∀ (G : Functor D Type_Cat) (GR : Representable G), is_Local_Right_KanExt p (FCOMP F G) (FCOMP lrke G).
  
End Pointwise_LRKE.

Section Pointwise_LLKE.
  Context {C C' : Category} {p : Functor C C'} {D: Category} {F : Functor C D} (llke : Local_Left_KanExt p F).
  
  Definition Pointwise_LLKE := ∀ (G : Functor D^op Type_Cat) (GR : CoRepresentable G), is_Local_Right_KanExt p (FCOMP F (FOP G)) (FOP (FCOMP llke G)).
  
End Pointwise_LLKE.