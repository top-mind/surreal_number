From SN Require Export base.

Notation Game := surreal.

From Stdlib Require Import Eqdep.

Ltac ginv H := inv H; do 2 match goal with
  | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H; subst
  end.
