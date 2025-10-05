(* SPDX-License-Identifier: Apache-2.0 *)
(* Kernel_API.v: Frozen IL exports for Phase-6 expressiveness *)
(* Re-exports IL-complete lemmas for downstream consumers *)
(* No admits; no classical dependencies *)

From PXLs Require Import
  phase6_expressiveness.PXL_Expressiveness_Boolean
  phase6_expressiveness.PXL_Expressiveness_NormalForms
  phase6_expressiveness.PXL_Expressiveness_ModalDuals
  phase6_expressiveness.PXL_Expressiveness_Filtration
  phase6_expressiveness.PXL_Expressiveness_Intertranslation.

(* Boolean layer *)
Export phase6_expressiveness.PXL_Expressiveness_Boolean.

(* Normal Forms: IL halves *)
Export phase6_expressiveness.PXL_Expressiveness_NormalForms (
  nnf_closed,
  nnf_exists,
  de_morgan_and_r,
  de_morgan_or_l,
  dia_to_not_box_not
).

(* Modal Duals: IL direction *)
Export phase6_expressiveness.PXL_Expressiveness_ModalDuals (
  dia_to_not_box_not
).

(* Filtration: Satisfiability form *)
Export phase6_expressiveness.PXL_Expressiveness_Filtration (
  filtration,
  fmp
).

(* Intertranslation: Soundness only *)
Export phase6_expressiveness.PXL_Expressiveness_Intertranslation (
  conserv_PXL_to_S5
).
