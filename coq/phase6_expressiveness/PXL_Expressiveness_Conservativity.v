(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_Conservativity.v *)
From PXLs Require Import PXLv3.
Notation "A â©ª B" := (Conj (Impl A B) (Impl B A)) (at level 70).

Fixpoint eliminate_macros (Ï†:form) : form :=
  match Ï† with
  | Conj a b => Neg (Impl (eliminate_macros a) (Neg (eliminate_macros b)))
  | Disj a b => Impl (Neg (eliminate_macros a)) (eliminate_macros b)
  | Dia a   => Neg (Box (Neg (eliminate_macros a)))
  | Neg a   => Neg (eliminate_macros a)
  | Impl a b=> Impl (eliminate_macros a) (eliminate_macros b)
  | Box a   => Box (eliminate_macros a)
  | _ as x  => x
  end.

Theorem macro_elim_roundtrip : forall Ï†, Prov (eliminate_macros Ï† â©ª Ï†). Admitted.
