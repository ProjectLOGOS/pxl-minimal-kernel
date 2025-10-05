(* SPDX-License-Identifier: Apache-2.0 *)
From Coq Require Import List.
Import ListNotations.
From PXLs Require Import PXLv3 PXL_Deep_Soundness Assumptions.

Lemma modal_dual_dia_box1 Ï† :
  Prov (Impl (Dia Ï†) (Neg (Box (Neg Ï†)))).
Proof. Admitted.

Lemma modal_dual_box_dia2 Ï† :
  Prov (Impl (Neg (Box Ï†)) (Dia (Neg Ï†))).
Proof. Admitted.

(* --- Basic sets and MCT structure with Hilbert closure --- *)

Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

Record mct (G:set) : Prop := {
  mct_cons  : consistent G;
  mct_thm   : forall Ï† : form, Prov Ï† -> G Ï†;                    (* theorems in the set *)
  mct_mp    : forall Ï† Ïˆ : form, G (Impl Ï† Ïˆ) -> G Ï† -> G Ïˆ;     (* closed under MP *)
  mct_total : forall Ï† : form, G Ï† \/ G (Neg Ï†)                  (* maximality *)
}.

(* --- Canonical worlds, accessibility --- *)

Definition world := { G : set | mct G }.

Definition can_R (w u:world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* --- Kripke forcing aligned with membership for Var --- *)

Fixpoint forces (w:world) (p:form) : Prop :=
  match p with
  | Bot      => False
  | Var n    => In_set (proj1_sig w) (Var n)
  | Impl a b => (forces w a -> forces w b)
  | And a b  => forces w a /\ forces w b
  | Or  a b  => forces w a \/ forces w b
  | Neg a    => ~ forces w a
  | Box a    => forall u, can_R w u -> forces u a
  | Dia a    => exists u, can_R w u /\ forces u a
  end.

(* --- Propositional helpers (from PXLv3 constructors) --- *)

Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
Proof. Admitted.

Lemma prov_or_imp_negL (a b : form) : Prov (Impl (Or a b) (Impl (Neg a) b)).
Proof. Admitted.

(* --- Canonical forcing respects Prov --- *)

Lemma can_R_box_elim Î“ Î” (HÎ“:mct Î“) (HÎ”:mct Î”) Ï† :
  can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”) -> In_set Î“ (Box Ï†) -> In_set Î” Ï†.
Proof. unfold can_R. simpl. firstorder. Qed.

Lemma explosion_from_neg_and_pos Î” (HÎ”:mct Î”) Ï† :
  In_set Î” (Neg Ï†) -> In_set Î” Ï† -> False.
Proof. intros H1 H2. destruct HÎ” as [Hcons _ _ _]. apply Hcons. exists Ï†. split; assumption. Qed.
