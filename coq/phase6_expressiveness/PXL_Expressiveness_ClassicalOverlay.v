(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_ClassicalOverlay.v *)
(* Classical extensions for Phase-6 expressiveness *)
(* Import kernel results and add classical halves *)

From PXLs Require Import PXLv3 Assumptions phase6_expressiveness.PXL_Expressiveness_NormalForms phase6_expressiveness.PXL_Expressiveness_ModalDuals phase6_expressiveness.PXL_Expressiveness_Conservativity.

Notation "A â©ª B" := (Conj (Impl A B) (Impl B A)) (at level 70).

Ltac MP H1 H2 := eapply mp; [exact H1|exact H2].

(* Classical axioms for overlay *)
Axiom ax_PL_dn : forall p, Prov (Impl (Neg (Neg p)) p).
Axiom ax_PL_em : forall p, Prov (Disj p (Neg p)).

(* Classical double negation left *)
Lemma dn_law_l Ï† : Prov (Impl (Neg (Neg Ï†)) Ï†).
Proof. exact (ax_PL_dn Ï†). Qed.

(* Classical De Morgan *)
Lemma de_morgan_and_l Ï† Ïˆ : Prov (Impl (Neg (Conj Ï† Ïˆ)) (Disj (Neg Ï†) (Neg Ïˆ))).
Proof.
  (* EM on Ï†: (Ï† âˆ¨ Â¬Ï†) *)
  pose proof (ax_PL_em Ï†) as EM.

  (* Branch 1: Ï† â†’ (Â¬Ï† âˆ¨ Â¬Ïˆ) *)
  (* Ï† â†’ (Ïˆ â†’ (Ï†âˆ§Ïˆ)) *)
  pose proof (ax_PL_and_intro Ï† Ïˆ) as Aintro.
  pose proof (ax_PL_imp Ï† Ïˆ (Conj Ï† Ïˆ)) as Cur1.
  pose proof (MP Cur1 Aintro) as H_ab.
  (* Â¬(Ï†âˆ§Ïˆ) â†’ ((Ï†âˆ§Ïˆ) â†’ âŠ¥) *)
  pose proof (ax_PL_neg_elim (Conj Ï† Ïˆ)) as NegAB.
  (* (Ï†âˆ§Ïˆ)â†’âŠ¥  â‡’  Â¬Ïˆ, then lift under Ï† *)
  pose proof (ax_PL_imp Ïˆ (Conj Ï† Ïˆ) Bot) as Cur2.
  pose proof (MP (ax_PL_imp_exch (Conj Ï† Ïˆ) Ïˆ Bot) NegAB) as BtoBot.
  pose proof (MP Cur2 BtoBot) as b_bot.
  pose proof (ax_PL_neg_intro Ïˆ) as NegIntroB.
  pose proof (MP (ax_PL_imp Ïˆ (Impl (Conj Ï† Ïˆ) Bot) (Neg Ïˆ)) NegIntroB) as to_nb.
  (* Ï† â†’ Â¬Ïˆ by composing Ï†â†’(Ïˆâ†’(Ï†âˆ§Ïˆ)) with (Ï†âˆ§Ïˆ)â†’âŠ¥ *)
  pose proof (ax_PL_imp Ï† (Impl Ïˆ (Conj Ï† Ïˆ)) (Impl Ïˆ Bot)) as Lift1.
  pose proof (MP Lift1 BtoBot) as a_b_bot.
  pose proof (ax_PL_imp Ï† (Impl Ïˆ Bot) (Neg Ïˆ)) as Lift2.
  pose proof (MP Lift2 NegIntroB) as a_nb.
  (* Â¬Ïˆ â†’ (Â¬Ï† âˆ¨ Â¬Ïˆ) *)
  pose proof (ax_PL_orI2 (Neg Ï†) (Neg Ïˆ)) as OrI2.
  pose proof (ax_PL_imp Ï† (Neg Ïˆ) (Disj (Neg Ï†) (Neg Ïˆ))) as Lift3.
  pose proof (MP Lift3 OrI2) as Branch1.  (* Ï† â†’ (Â¬Ï† âˆ¨ Â¬Ïˆ) *)

  (* Branch 2: Â¬Ï† â†’ (Â¬Ï† âˆ¨ Â¬Ïˆ) *)
  pose proof (ax_PL_orI1 (Neg Ï†) (Neg Ïˆ)) as Branch2.       (* Â¬Ï† â†’ (Â¬Ï† âˆ¨ Â¬Ïˆ) *)

  (* Or-elim combiner: (Ï†â†’R) â†’ ((Â¬Ï†â†’R) â†’ ((Ï†âˆ¨Â¬Ï†)â†’R)) *)
  pose proof (ax_PL_orE Ï† (Neg Ï†) (Disj (Neg Ï†) (Neg Ïˆ))) as OrE.
  pose proof (MP (MP OrE Branch1) Branch2) as EM_to_R.       (* (Ï†âˆ¨Â¬Ï†)â†’R *)

  (* Feed EM after rotating antecedents to make Â¬(Ï†âˆ§Ïˆ) first *)
  pose proof (ax_PL_k (Disj (Neg Ï†) (Neg Ïˆ)) (Neg (Conj Ï† Ïˆ))) as K1.
  pose proof (ax_PL_imp_exch (Disj (Neg Ï†) (Neg Ïˆ)) (Neg (Conj Ï† Ïˆ)) (Disj (Neg Ï†) (Neg Ïˆ))) as Ex1.
  pose proof (MP Ex1 K1) as NegAB_to_EM.
  pose proof (ax_PL_imp (Neg (Conj Ï† Ïˆ)) (Disj Ï† (Neg Ï†)) (Disj (Neg Ï†) (Neg Ïˆ))) as Cur4.
  pose proof (MP Cur4 EM_to_R) as NegAB_to_R.
  exact (MP NegAB_to_R NegAB_to_EM).
Qed.

Lemma dia_to_not_box_not Ï† : Prov (Impl (Dia Ï†) (Neg (Box (Neg Ï†)))).
Proof. exact (ax_modal_dual_dia_box2 Ï†). Qed.

Lemma not_box_not_to_dia Ï† : Prov (Impl (Neg (Box (Neg Ï†))) (Dia Ï†)).
Proof. exact (ax_modal_dual_box_dia1 (Neg Ï†)). Qed.

(* Full equivalences using kernel + overlay halves *)
Lemma double_neg_equiv Ï† : Prov (Neg (Neg Ï†) â©ª Ï†).
Proof.
  eapply mp; [eapply mp; [exact (ax_PL_and_intro (Impl (Neg (Neg Ï†)) Ï†) (Impl Ï† (Neg (Neg Ï†)))) | exact (dn_law_l Ï†)] | exact (dn_law_r Ï†)].
Qed.

Lemma de_morgan_and_equiv Ï† Ïˆ : Prov (Neg (Conj Ï† Ïˆ) â©ª Disj (Neg Ï†) (Neg Ïˆ)).
Proof.
  eapply mp; [eapply mp; [exact (ax_PL_and_intro (Impl (Neg (Conj Ï† Ïˆ)) (Disj (Neg Ï†) (Neg Ïˆ))) (Impl (Disj (Neg Ï†) (Neg Ïˆ)) (Neg (Conj Ï† Ïˆ)))) | exact (de_morgan_and_l Ï† Ïˆ)] | exact (de_morgan_and_r Ï† Ïˆ)].
Qed.

Lemma dia_macro_equiv Ï† : Prov (Dia Ï† â©ª Neg (Box (Neg Ï†))).
Proof.
  eapply mp; [eapply mp; [exact (ax_PL_and_intro (Impl (Dia Ï†) (Neg (Box (Neg Ï†)))) (Impl (Neg (Box (Neg Ï†))) (Dia Ï†))) | exact (dia_to_not_box_not Ï†)] | exact (not_box_not_to_dia Ï†)].
Qed.

(* Classical macro elimination roundtrip *)
Theorem macro_elim_roundtrip Ï† : Prov (eliminate_macros Ï† â©ª Ï†).
Admitted.
