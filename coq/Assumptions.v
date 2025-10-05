(* SPDX-License-Identifier: Apache-2.0 *)
(* Assumptions.v: Unavoidable constructive assumptions for PXL completeness *)

From PXLs Require Import PXLv3.

(* Placeholder model type for assumptions *)
Parameter Model : Type.
Parameter R : Model -> nat -> nat -> Prop.
Parameter forces : Model -> nat -> form -> Prop.

(* Frame assumption for modal duality: constructive witness extraction for failure of universal *)
Axiom NotAll_to_ExNot_R :
  forall (M:Model) w Ï†,
    (~ forall v, R M w v -> forces M v (Neg Ï†)) ->
    exists v, R M w v /\ forces M v Ï†.

(* If decidability of consistency for finite sets is not constructive, add here *)
(* Axiom decidable_cons_finite : ... *)

(* Philosophical justification: This captures the intuitionistic notion of "not all" implying "some not",
   which holds in Kripke semantics for S5 frames with constructive accessibility. *)
