(* SPDX-License-Identifier: Apache-2.0 *)
From PXLs Require Import PXLv3.

(* Derivable from Hilbert propositional axioms *)

Lemma box_imp_r (Ï† Ïˆ : form) : Prov (Impl Ï† Ïˆ) -> Prov (Impl (Box Ï†) (Box Ïˆ)).
Proof.
  intros H.
  pose (H1 := nec H).
  pose (H2 := ax_K Ï† Ïˆ).
  eapply mp; eauto.
Qed.

Lemma priv_absent (Ï† : form) : Prov (Nec (Impl (Impl Ï† Bot) (Impl Ï† Bot))).
Proof.
  pose (X := Impl Ï† Bot).
  pose proof (id_prop X) as H.
  exact (nec H).
Qed.



