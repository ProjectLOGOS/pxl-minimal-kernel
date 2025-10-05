(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_NormalForms.v *)
From PXLs Require Import PXLv3 Assumptions PXL_Expressiveness_ModalDuals.

Notation "A â©ª B" := (Conj (Impl A B) (Impl B A)) (at level 70).

(* classical assumptions exported by Assumptions.v *)
(* ax_PL_em  : forall p, Prov (Disj p (Neg p)). *)
(* ax_PL_dn  : forall p, Prov (Impl (Neg (Neg p)) p). *)

(* a -> Â¬Â¬a, derivable intuitionistically *)
Lemma dn_law_r : forall a, Prov (Impl a (Neg (Neg a))).
Proof.
  Admitted.

Lemma dn_law_l : forall a, Prov (Impl (Neg (Neg a)) a).
Proof. Admitted.

(* De Morgan: Â¬(a âˆ§ b) -> (Â¬a âˆ¨ Â¬b), classical via EM on a *)
Lemma de_morgan_and_l : forall a b, Prov (Impl (Neg (Conj a b)) (Disj (Neg a) (Neg b))).
Proof.
  Admitted.
  
(* De Morgan: (Â¬a âˆ¨ Â¬b) -> Â¬(a âˆ§ b) *)
Lemma de_morgan_and_r : forall a b, Prov (Impl (Disj (Neg a) (Neg b)) (Neg (Conj a b))).
Proof.
  Admitted.

(* De Morgan: Â¬(a âˆ¨ b) <-> (Â¬a âˆ§ Â¬b) *)
Lemma de_morgan_or_l  : forall a b, Prov (Impl (Neg (Disj a b)) (Conj (Neg a) (Neg b))).
Proof.
  intros a b.
  (* part 1: Â¬(aâˆ¨b) â†’ Â¬a *)
  pose proof (ax_PL_orI1 a b) as OrI1ab.                   (* a â†’ (aâˆ¨b) *)
  pose proof (ax_PL_imp (Neg (Disj a b)) a (Neg a)) as CurA1.
  pose proof (MP CurA1 (ax_PL_neg_elim (Disj a b))) as HNa. (* Â¬(aâˆ¨b) â†’ Â¬a *)

  (* part 2: Â¬(aâˆ¨b) â†’ Â¬b *)
  pose proof (ax_PL_orI2 a b) as OrI2ab.                   (* b â†’ (aâˆ¨b) *)
  pose proof (ax_PL_imp (Neg (Disj a b)) b (Neg b)) as CurA2.
  pose proof (MP CurA2 (ax_PL_neg_elim (Disj a b))) as HNb. (* Â¬(aâˆ¨b) â†’ Â¬b *)

  (* combine to conjunction *)
  pose proof (ax_PL_and_intro (Neg a) (Neg b)) as AndIntro.
  (* curry: (pâ†’q) â†’ ((pâ†’r) â†’ (pâ†’(qâˆ§r))) with p:=Â¬(aâˆ¨b) *)
  pose proof (ax_PL_imp (Neg (Disj a b)) (Neg a) (Impl (Neg (Disj a b)) (Neg b))) as Cur1.
  pose proof (MP Cur1 (ax_PL_imp_exch (Neg (Disj a b)) (Neg a) (Neg b))) as Cur2.
  pose proof (MP (ax_PL_imp (Neg (Disj a b)) (Neg b) (Conj (Neg a) (Neg b))) AndIntro) as Cur3.
  pose proof (MP Cur2 HNa) as P1.
  exact (MP P1 HNb).
Qed.
Lemma de_morgan_or_r  : forall a b, Prov (Impl (Conj (Neg a) (Neg b)) (Neg (Disj a b))).
Admitted.

Lemma dia_macro : forall a, Prov (Dia a â©ª Neg (Box (Neg a))).
Proof. Admitted.

Inductive nnf : form -> Prop :=
| N_Atom    : forall n, nnf (Atom n)
| N_Bot     : nnf Bot
| N_NegAtom : forall n, nnf (Neg (Atom n))
| N_NegBot  : nnf (Neg Bot)
| N_And     : forall a b, nnf a -> nnf b -> nnf (Conj a b)
| N_Or      : forall a b, nnf a -> nnf b -> nnf (Disj a b)
| N_Box     : forall a, nnf a -> nnf (Box a)
| N_Dia     : forall a, nnf a -> nnf (Dia a).

Fixpoint nnfify (Ï† : form) : form :=
  match Ï† with
  | Atom n => Atom n
  | Bot => Bot
  | Neg Ïˆ => nnf_neg Ïˆ
  | Conj a b => Conj (nnfify a) (nnfify b)
  | Disj a b => Disj (nnfify a) (nnfify b)
  | Impl a b => Disj (nnf_neg a) (nnfify b)
  | Box Ïˆ => Box (nnfify Ïˆ)
  | Dia Ïˆ => Dia (nnfify Ïˆ)
  end
with nnf_neg (Ï† : form) : form :=
  match Ï† with
  | Atom n => Neg (Atom n)
  | Bot => Neg Bot
  | Neg Ïˆ => nnfify Ïˆ
  | Conj a b => Disj (nnf_neg a) (nnf_neg b)
  | Disj a b => Conj (nnf_neg a) (nnf_neg b)
  | Impl a b => Conj (nnfify a) (nnf_neg b)
  | Box Ïˆ => Dia (nnf_neg Ïˆ)
  | Dia Ïˆ => Box (nnf_neg Ïˆ)
  end.

Lemma nnf_closed : forall Ï†, nnf (nnfify Ï†)
with nnf_neg_closed : forall Ï†, nnf (nnf_neg Ï†).
Proof.
  - induction Ï†; cbn.
    + apply N_Atom.
    + apply N_Bot.
    + apply nnf_neg_closed.
    + apply N_And; auto.
    + apply N_Or; auto.
    + apply N_Or; auto.
    + apply N_Box; auto.
    + apply N_Dia; auto.
  - induction Ï†; cbn.
    + apply N_NegAtom.
    + apply N_NegBot.
    + apply nnf_closed.
    + apply N_Or; auto.
    + apply N_And; auto.
    + apply N_And; auto.
    + apply N_Dia; auto.
    + apply N_Box; auto.
Qed.

Lemma double_neg_equiv : forall a, Prov (Neg (Neg a) â©ª a).
Proof.
  intros a.
  eapply mp; [eapply mp; [exact (ax_PL_and_intro (Impl (Neg (Neg a)) a) (Impl a (Neg (Neg a)))) | exact (dn_law_l a)] | exact (dn_law_r a)].
Qed.

Lemma de_morgan_and_equiv : forall a b, Prov (Neg (Conj a b) â©ª Disj (Neg a) (Neg b)).
Proof. Admitted.

Lemma de_morgan_or_equiv : forall a b, Prov (Neg (Disj a b) â©ª Conj (Neg a) (Neg b)).
Proof. Admitted.

Lemma dia_macro_equiv : forall a, Prov (Dia a â©ª Neg (Box (Neg a))).
Proof. Admitted.

Theorem nnf_exists : forall Ï†, exists Ï†', Prov (Ï† â©ª Ï†') /\ nnf Ï†'.
Proof. Admitted.
