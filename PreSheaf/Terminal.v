Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Basic_Cons.Terminal.
Require Import PreSheaf.PreSheaf.

Section Terminal.
  Context (C : Category).

  (** The terminal element of the category of presheaves. *)
  Program Definition PSh_Term_PreSheaf : Functor (C^op) Type_Cat :=
    {|
      FO := fun _ => unit
    |}.

  Local Hint Resolve NatTrans_eq_simplify.
  Local Hint Extern 1 =>
  match goal with
    [|- ?A = ?B] => try destruct A; try destruct B; trivial; fail
  end.  

  (** The functor that maps to the unit type in coq is the terminal object
      of presheaves. *)
  Program Instance PSh_Terminal : (𝟙_ (PShCat C))%object :=
    {
      terminal := PSh_Term_PreSheaf;
      t_morph := fun _ => {|Trans := fun _ _ => tt|}
    }.

End Terminal.
