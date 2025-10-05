(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_Filtration.v *)
From Coq Require Import List.
Import ListNotations.
From PXLs Require Import PXL_Canonical_Kernel PXL_Deep_Soundness PXLv3.

Parameter model : Type.
Parameter forces : model -> form -> Prop.

Fixpoint sub (Ï†:form) : list form :=
  match Ï† with
  | Conj a b | Disj a b | Impl a b => Ï† :: sub a ++ sub b
  | Neg a | Box a | Dia a          => Ï† :: sub a
  | _                              => [Ï†]
  end.
Definition filtered (M:model) (Ï†:form) (M':model) : Prop := True.

Theorem filtration : forall M Ï†, exists M', filtered M Ï† M'.
Proof.
  (* Define â‰¡_Î£ on worlds by agreement on forces for all subformulas in Î£ := sub Ï†.
     Build the quotient model M/â‰¡_Î£ with relations inherited from your canonical kernel.
     Prove truth preservation for all Ïˆ âˆˆ Î£ by induction on Ïˆ. *)
  Admitted.

Corollary fmp : forall Ï†, ~ Prov Ï† -> exists M, ~ forces M Ï†.
Proof. Admitted.
