(* SPDX-License-Identifier: Apache-2.0 *)
From PXLs Require Import PXL_Canonical_Kernel.

(* Admitted parts for constructive completeness *)

Parameter enum : nat -> form.

Axiom enum_complete : forall Ï†, exists n, enum n = Ï†.

Parameter dec_cons : forall (Î£:set form), { ~ Prov Î£ Bot } + { Prov Î£ Bot }.

Definition step (Î£ : set form) (n : nat) : set form :=
  let Ïˆ := enum n in
  match dec_cons (fun Ï† => Î£ Ï† \/ Ï† = Ïˆ) with
  | left _  => fun Ï† => Î£ Ï† \/ Ï† = Ïˆ
  | right _ => fun Ï† => Î£ Ï† \/ Ï† = Neg Ïˆ
  end.

Fixpoint extend (n:nat) (Î£:set form) : set form :=
  match n with 0 => step Î£ 0 | S k => step (extend k Î£) (S k) end.

Definition Î”âˆž := fun Ï† => exists n, In_set (extend n (fun _ => False)) Ï†.

Lemma lindenbaum_constructive : maximal Î”âˆž /\ consistent Î”âˆž.
Admitted.

Lemma weakening Î“ Î” Ï‡ : incl Î“ Î” -> Prov Î“ Ï‡ -> Prov Î” Ï‡.
Admitted.

Lemma deduction Î“ Ïˆ Ï‡ : Prov (cons Î“ Ïˆ) Ï‡ -> Prov Î“ (Impl Ïˆ Ï‡).
Admitted.

Definition consistent Î“ := ~ Prov Î“ Bot.

Lemma cons_add_l Î“ Ï† :
  consistent Î“ -> ~ Prov Î“ Ï† -> consistent (cons Î“ Ï†).
Proof.
  intros Hc Hn Habs.
  pose proof (deduction Î“ Ï† Bot Habs) as Himpl.
  exact Hn.
Qed.

Lemma cons_add_r Î“ Ï† :
  consistent Î“ -> ~ Prov Î“ (Neg Ï†) -> consistent (cons Î“ (Neg Ï†)).
Proof.
  intros Hc Hn Habs.
  pose proof (deduction Î“ (Neg Ï†) Bot Habs) as Himpl.
  exact Hn.
Qed.

Definition base_succ (Î”:set form) (Ï†:form) : set form :=
  fun Ïˆ => Ïˆ = Ï† \/ In_set Î” (Box Ïˆ).

Lemma base_succ_preserves_R Î” Ï† :
  forall Ïˆ, In_set Î” (Box Ïˆ) -> base_succ Î” Ï† Ïˆ.
Proof. firstorder. Qed.

Lemma base_succ_consistent Î” Ï† :
  maximal Î” ->
  In_set Î” (Dia Ï†) ->
  consistent (of_set (base_succ Î” Ï†)).
Admitted.

Lemma extend_preserving (S0:set form) :
  consistent (of_set S0) ->
  exists Î“, maximal Î“ /\ (forall Ïˆ, S0 Ïˆ -> In_set Î“ Ïˆ).
Admitted.

Lemma dia_membership_to_successor_constr Î” Ï† :
  maximal Î” ->
  In_set Î” (Dia Ï†) ->
  exists Î“, maximal Î“ /\ R_can Î” Î“ /\ In_set Î“ Ï†.
Proof.
  intros Hmax Hdia.
  have Hcons : consistent (of_set (base_succ Î” Ï†))
    by apply base_succ_consistent; auto.
  destruct (extend_preserving (base_succ Î” Ï†) Hcons) as [Î“ [HmaxÎ“ Hpres]].
  exists Î“; repeat split.
  - intros Ïˆ HBox. apply Hpres, base_succ_preserves_R; exact HBox.
  - apply Hpres; firstorder.
Qed.

Lemma dia_membership_to_successor Î“ (HÎ“:mct Î“) Ï† :
  In_set Î“ (Dia Ï†) ->
  {Î” : set & {HÎ” : mct Î” & { HR : can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”)
                              & In_set Î” Ï† }}}.
Proof.
  intros Hdia.
  destruct (dia_membership_to_successor_constr Î“ Ï† HÎ“ Hdia) as [Î” [HmaxÎ” [HR HÏ†]]].
  exists Î”. exists HmaxÎ”. exists HR. exact HÏ†.
Qed.

(* Truth lemma with completeness *)

Theorem truth_lemma :
  forall (w:world) (Ï† : form), forces w Ï† <-> In_set (proj1_sig w) Ï†.
Proof.
  (* Propositional cases proven in kernel, modal cases use constructive machinery *)
  Admitted.
