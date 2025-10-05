(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Expressiveness_Boolean.v *)
From PXLs Require Import PXLv3 Assumptions.

Section BooleanDefs.
  Variables Ï† Ïˆ r : form.
  Notation "A â©ª B" := (Conj (Impl A B) (Impl B A)) (at level 70).

  Definition Top  : form := Impl Ï† (Impl Ï† Ï†).
  Definition Bot  : form := Neg Top.
  Definition AndC (Ï† Ïˆ:form) : form := Conj Ï† Ïˆ.
  Definition OrC  (Ï† Ïˆ:form) : form := Disj Ï† Ïˆ.

  Tactic Notation "MP" constr(H1) constr(H2) := eapply mp; [exact H1|exact H2].

  Lemma top_taut : Prov Top.
  Proof.
    (* Instance of K with p:=Ï†, q:=Ï†, then use exchange to get Ï†â†’Ï† if needed. *)
    exact (ax_PL_k Ï† Ï†).
  Qed.

  Lemma andc_intro : Prov (Impl Ï† (Impl Ïˆ (AndC Ï† Ïˆ))).
  Proof. exact (ax_PL_and_intro Ï† Ïˆ). Qed.

  Lemma andc_elim_l : Prov (Impl (AndC Ï† Ïˆ) Ï†).
  Proof. exact (ax_PL_and1 Ï† Ïˆ). Qed.

  Lemma andc_elim_r : Prov (Impl (AndC Ï† Ïˆ) Ïˆ).
  Proof. exact (ax_PL_and2 Ï† Ïˆ). Qed.

  Lemma or_intro_l : Prov (Impl Ï† (OrC Ï† Ïˆ)).
  Proof.
    exact (ax_PL_orI1 Ï† Ïˆ).
  Qed.

  Lemma or_elim : Prov (Impl (OrC Ï† Ïˆ) (Impl (Impl Ï† r) (Impl (Impl Ïˆ r) r))).
  Proof.
    set (X := Impl Ï† r).
    set (Y := Impl Ïˆ r).
    set (Z := Disj Ï† Ïˆ).

    (* H0: X -> (Y -> (Z -> r)) *)
    pose proof (ax_PL_orE Ï† Ïˆ r) as H0.

    (* swap X,Y *)
    pose proof (ax_PL_imp_exch X Y (Impl Z r)) as E1.
    pose proof (mp E1 H0) as H1.                         (* Y -> (X -> (Z -> r)) *)

    (* swap back to X -> Y -> ... (just to match the next lift cleanly) *)
    pose proof (ax_PL_imp_exch Y X (Impl Z r)) as E1'.
    pose proof (mp E1' H1) as H1'.                       (* X -> (Y -> (Z -> r)) *)

    (* rotate Y,(Z->r)  under leading X *)
    pose proof (ax_PL_imp_exch Y Z r) as EZY.            (* (Y->Z->r) -> (Z->Y->r) *)
    pose proof (ax_PL_imp X (Impl Y (Impl Z r)) (Impl Z (Impl Y r))) as L1.
    pose proof (mp L1 H1') as Temp.                      (* ... -> X -> (Z -> Y -> r) *)
    pose proof (mp Temp EZY) as H2.                      (* X -> (Z -> Y -> r) *)

    (* bring Z to the front *)
    pose proof (ax_PL_imp_exch X Z (Impl Y r)) as EXZ.
    pose proof (mp EXZ H2) as H3.                        (* Z -> (X -> (Y -> r)) *)

    unfold X, Y, Z in H3; exact H3.
  Qed.
End BooleanDefs.
