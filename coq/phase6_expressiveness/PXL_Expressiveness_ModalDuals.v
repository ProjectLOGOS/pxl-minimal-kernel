(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_ModalDuals.v *)
From PXLs Require Import PXLv3 PXL_Deep_Soundness Assumptions PXL_Canonical_Kernel.

(* Equivalence as a formula over {Impl, Neg, And} *)
Notation "A â©ª B" := (And (Impl A B) (Impl B A)) (at level 70).

Section ModalDuals.
  Variable Ï† : form.

  (* Phase-6 chooses Dia as a macro over Box. *)
  Definition Dia_def (Ïˆ:form) : form := Neg (Box (Neg Ïˆ)).

  (* If Dia is just a notation, rewrite is definitional and this is immediate.
     If Dia is a real constructor, keep Dia_def and prove both implications
     from your K/T/5 propositional base. *)
  Lemma dia_dual_equiv : Prov (Dia Ï† â©ª Dia_def Ï†).
  Proof.
    (* left: Dia Ï† -> Â¬â–¡Â¬Ï†, right: Â¬â–¡Â¬Ï† -> Dia Ï† *)
    (* discharge with your existing modal/propositional lemmas *)
    Admitted.
End ModalDuals.
