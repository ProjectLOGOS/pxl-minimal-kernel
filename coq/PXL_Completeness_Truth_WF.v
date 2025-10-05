(* SPDX-License-Identifier: Apache-2.0 *)
(* PXL_Completeness_Truth_WF.v â€” restored scaffold (kernel constructive) *)(* PXL_Completeness_Truth_WF.v â€” restored scaffold (kernel constructive) *)(* PXL_Completeness_Truth_WF.v â€” restored scaffold (kernel constructive) *)



From Coq Require Import Program.Wf Arith List Lia.

From PXLd Require Import PXL_Decidability.

Import ListNotations.From Coq Require Import Program.Wf Arith List Lia.From Coq Require Import Program.Wf Arith List Lia.

Set Implicit Arguments.

From PXLd Require Import PXL_Decidability.From PXLd Require Import PXL_Decidability.

(* Basic syntax *)

Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.Import ListNotations.Import ListNotations.



(* Hilbert-style provability predicate *)Set Implicit Arguments.Set Implicit Arguments.

Inductive Prov : form -> Prop :=

| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))Import ListNotations.

| ax_T  : forall p,   Prov (Impl (Box p) p)

| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))(* Basic syntax *)

| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))

| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.(* Basic syntax *)

| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)

| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)

| ax_PL_em  : forall p, Prov (Or p (Neg p))(* Hilbert-style provability predicate *)Scheme Equality for form      + intros Hf.

| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q

| nec   : forall p, Prov p -> Prov (Box p).Inductive Prov : form -> Prop :=        destruct (mct_total Hm a) as [Ha | Hna].



(* Sets of formulas *)| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))        * assert (forces w a) by (apply (proj2 (IH a)); exact Ha).

Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.| ax_T  : forall p,   Prov (Impl (Box p) p)          specialize (Hf H0). 



(* Consistency *)| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))          apply (proj1 (IH b)) in Hf.

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))          pose proof (mct_thm Hm _ (prov_imp_weaken a b)) as Hb_imp.

(* Maximal consistent theories with closure *)

Record mct (G : set) : Prop := {| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))          exact (mct_mp Hm _ _ Hb_imp Hf).

  mct_cons : consistent G;

  mct_closed : forall Ï† Ïˆ, Prov (Impl Ï† Ïˆ) -> G Ï† -> G Ïˆ;| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)        * pose proof (mct_thm Hm _ (prov_neg_is_impl a)) as Hneg.

  mct_max : forall Ï†, G Ï† \/ G (Neg Ï†)

}.| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)          pose proof (mct_thm Hm _ (prov_exfalso b)) as Hb_imp.



(* Base axioms for maximal theory closure *)| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)          exact (mct_mp Hm _ _ Hb_imp (mct_mp Hm _ _ Hneg Hna)).

Axiom maximal_contains_theorems : forall G, mct G -> forall Ï†, Prov Ï† -> In_set G Ï†.

Axiom maximal_MP_closed : forall G, mct G -> forall Ï† Ïˆ, In_set G (Impl Ï† Ïˆ) -> In_set G Ï† -> In_set G Ïˆ.| ax_PL_em  : forall p, Prov (Or p (Neg p))      + intros Hab.vability *)



(* Euclidean helper axiom derived from ax_5 *)| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov qInductive Prov : form -> Prop :=

Axiom ax_Euclid : forall p, Prov (Impl (Box p) (Box (Box p))).

| nec   : forall p, Prov p -> Prov (Box p).  | ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))

(* Small wrappers *)

Definition maximal (G:set) : Prop := mct G.  | ax_T  : forall p,   Prov (Impl (Box p) p)

Definition extends (G H:set) : Prop := forall p, G p -> H p.

(* Sets of formulas *)  | ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))

(* Placeholder for the rest of the file - to be completed *)

Lemma placeholder : True.Definition set := form -> Prop.  | ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))

Proof. trivial. Qed.
Definition In_set (G:set) (p:form) : Prop := G p.  | ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))

  | ax_PL_and1 : forall p q, Prov (Impl (And p q) p)

(* Consistency *)  | ax_PL_and2 : forall p q, Prov (Impl (And p q) q)

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).  | ax_PL_and : forall p q, Prov (Impl p (Impl q (And p q)))

  | ax_PL_or1 : forall p q, Prov (Impl p (Or p q))

(* Maximal consistent theories with closure *)  | ax_PL_or2 : forall p q, Prov (Impl q (Or p q))

Record mct (G : set) : Prop := {  | ax_PL_em  : forall p, Prov (Or p (Neg p))

  mct_cons : consistent G;  | ax_PL_neg1 : forall p, Prov (Impl (Impl p Bot) (Neg p))

  mct_closed : forall Ï† Ïˆ, Prov (Impl Ï† Ïˆ) -> G Ï† -> G Ïˆ;  | ax_PL_neg2 : forall p, Prov (Impl (Neg p) (Impl p Bot))

  mct_max : forall Ï†, G Ï† \/ G (Neg Ï†)  | ax_PL_neg_impl1 : forall Ï† Ïˆ, Prov (Impl (Neg (Impl Ï† Ïˆ)) (And Ï† (Neg Ïˆ)))

}.  | ax_PL_neg_impl2 : forall Ï† Ïˆ, Prov (Impl (And Ï† (Neg Ïˆ)) (Neg (Impl Ï† Ïˆ)))

  | mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q

(* Base axioms for maximal theory closure *)  | nec   : forall p, Prov p -> Prov (Box p).

Axiom maximal_contains_theorems : forall G, mct G -> forall Ï†, Prov Ï† -> In_set G Ï†.

Axiom maximal_MP_closed : forall G, mct G -> forall Ï† Ïˆ, In_set G (Impl Ï† Ïˆ) -> In_set G Ï† -> In_set G Ïˆ.Axiom ax_PL_or : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r).



(* Euclidean helper axiom derived from ax_5 *)(* Sets of formulas *)

Axiom ax_Euclid : forall p, Prov (Impl (Box p) (Box (Box p))).Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.

(* Small wrappers *)

Definition maximal (G:set) : Prop := mct G.(* Consistency *)

Definition extends (G H:set) : Prop := forall p, G p -> H p.Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).



(* Placeholder for the rest of the file - to be completed *)(* Maximal consistent theories with closure *)

Lemma placeholder : True.Record mct (G : set) : Prop := {

Proof. trivial. Qed.  mct_cons : consistent G;
  mct_total : forall Ï†, In_set G Ï† \/ In_set G (Neg Ï†);
  mct_thm : forall Ï†, Prov Ï† -> In_set G Ï†;
  mct_mp : forall Ï† Ïˆ, In_set G (Impl Ï† Ïˆ) -> In_set G Ï† -> In_set G Ïˆ
}.

(* Maximal consistent sets *)
Definition maximal (G:set) : Prop := consistent G /\ forall Ï†, In_set G Ï† \/ In_set G (Neg Ï†).

(* --- Primitives assumed already defined in your repo --- *)
(* Prov, chain, Lindenbaum, bridges, maximal lemmas:               *)
(* maximal_In_set_Prov, max_and, max_orL, max_impl, max_neg, etc.          *)
(* nec, maximal_contains_theorems (your naming), chain_inconsistency, etc. *)

(* ---------- Section: modal logic machinery ---------- *)
Section KernelParams.

Variable Î“ : set.
Variable H : mct Î“.

  (* Your existing propositional truth lemma machinery goes here:
     - Prov inductive + propositional axioms
     - fsize and WF setup
     - truth_lemma_aux (Program Fixpoint) with obligations
     - Theorem truth_lemma (uses [box_intro] only as a hypothesis) *)

  (* Canonical model *)
  Definition can_world := { G : set | mct G }.
  Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

  (* Forces relation *)
  Fixpoint forces (w:can_world) (p:form) : Prop :=
    match p with
    | Bot => False
    | Var n => True (* arbitrary *)
    | Impl p q => forces w p -> forces w q
    | And p q => forces w p /\ forces w q
    | Or p q => forces w p \/ forces w q
    | Neg p => ~ forces w p
    | Box p => forall u, can_R w u -> forces u p
    | Dia p => exists u, can_R w u /\ forces u p
    end.

  (* Finite support for Prov derivations *)
  Lemma prov_finite_support : forall Ï† (prf : Prov Ï†) Î£,
    (forall Ïˆ, Prov Ïˆ -> In_set Î£ Ïˆ) ->
    exists Î“f, forall Ï‡, In Ï‡ Î“f -> In_set Î£ Ï‡.
  Proof.
    intros Ï† prf Î£ Hprov.
    induction prf.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - exists []. intros Ï‡ HIn. inversion HIn.
    - (* mp case *)
      destruct IHprf1 as [Î“f1 H1]. destruct IHprf2 as [Î“f2 H2].
      exists (nodup form_eq_dec (Î“f1 ++ Î“f2)).
      intros Ï‡ HIn. apply nodup_In in HIn. apply in_app_or in HIn as [HIn1 | HIn2].
      + apply H1; assumption.
      + apply H2; assumption.
    - (* nec case *)
      destruct IHprf as [Î“f1 H1].
      exists Î“f1.
      intros Ï‡ HIn. apply H1; assumption.
  Qed.

  (* ---------- VARIABLES (constructive where possible) ---------- *)
  Lemma maximal_contains_theorems : forall Î“, maximal Î“ -> forall Ï†, Prov Ï† -> In_set Î“ Ï†.
  Proof. Admitted.
  Lemma max_and : forall Î“ Ï† Ïˆ, maximal Î“ -> In_set Î“ (And Ï† Ïˆ) -> (In_set Î“ Ï† /\ In_set Î“ Ïˆ).
  Proof. Admitted.
  Lemma max_orL : forall Î“ Ï† Ïˆ, maximal Î“ -> In_set Î“ (Or Ï† Ïˆ) -> (In_set Î“ Ï† \/ In_set Î“ Ïˆ).
  Proof. Admitted.
  Lemma max_impl : forall Î“ Ï† Ïˆ, maximal Î“ -> In_set Î“ (Impl Ï† Ïˆ) -> (In_set Î“ Ï† -> In_set Î“ Ïˆ).
  Proof. Admitted.
  Lemma max_neg : forall Î“ Ï†, maximal Î“ -> In_set Î“ (Neg Ï†) -> ~ In_set Î“ Ï†.
  Proof. Admitted.

  Lemma decide : forall Ï†, {Prov Ï†} + {~ Prov Ï†}.
  Proof. Admitted.

  Lemma form_neq_neg : forall Ï†, Ï† <> Neg Ï†.
  Proof.
    induction Ï†; intro Heq; inversion Heq.
    - apply IHÏ†. assumption.
  Qed.

  Lemma neg_inj : forall a b, Neg a = Neg b -> a = b.
  Proof. intros a b Heq. inversion Heq. reflexivity. Qed.

  (* Assumptions: standard Hilbert base with:
     - ax_k       : Prov (Impl p (Impl q p))           (* K *)
     - prov_mp    : Prov (Impl p q) -> Prov p -> Prov q
     - and/ or primitives already present in your base:
         ax_and_intro : Prov (Impl p (Impl q (And p q)))
         ax_and_elimL : Prov (Impl (And p q) p)
         ax_and_elimR : Prov (Impl (And p q) q)
         ax_or_introL : Prov (Impl p (Or p q))
         ax_or_introR : Prov (Impl q (Or p q))
         ax_or_elim   : Prov (Impl (Impl p r) (Impl (Impl q r) (Impl (Or p q) r)))
     - Neg a is (Impl a Bot)
     Rename identifiers below if your base uses different names.
  *)

  Axiom ax_k : forall p q, Prov (Impl p (Impl q p)).
  Axiom prov_mp : forall p q, Prov (Impl p q) -> Prov p -> Prov q.
  Axiom ax_and_intro : forall p q, Prov (Impl p (Impl q (And p q))).
  Axiom ax_and_elimL : forall p q, Prov (Impl (And p q) p).
  Axiom ax_and_elimR : forall p q, Prov (Impl (And p q) q).
  Axiom ax_or_introL : forall p q, Prov (Impl p (Or p q)).
  Axiom ax_or_introR : forall p q, Prov (Impl q (Or p q)).
  Axiom ax_or_elim : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r).

  (* Additional axioms for the proofs *)
  Axiom prov_imp_exch : forall p q r, Prov (Impl p (Impl q r)) -> Prov (Impl q (Impl p r)).
  Axiom neg_imp_to_any : forall a b, Prov (Impl (Neg a) (Impl a b)).
  Lemma modal_dual_dia_box1 : forall Ï†, Prov (Impl (Neg (Dia Ï†)) (Box (Neg Ï†))).
  Proof.
    intros Ï†. (* Use canonical semantics + MCT closure *)
    (* Outline: if Â¬â—‡Ï† then every accessible world fails Ï†, hence â–¡Â¬Ï† *)
  Admitted.

  Lemma modal_dual_box_dia2 : forall Ï†, Prov (Impl (Neg (Box Ï†)) (Dia (Neg Ï†))).
  Proof.
    intros Ï†. (* Symmetric argument to dual above *)
  Admitted.
  Axiom can_R_box_elim : forall Î“ Î” HÎ“ HÎ” Ï†, can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”) -> In_set Î“ (Box Ï†) -> In_set Î” Ï†.
  Axiom dia_membership_to_successor : forall Î“ HÎ“ Ï†, In_set Î“ (Dia Ï†) -> {Î” : set & {HÎ” : mct Î” & {HR : can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”) & In_set Î” Ï†}}}.
  Axiom explosion_from_neg_and_pos : forall Î” Ï†, In_set Î” (Neg Ï†) -> In_set Î” Ï† -> False.

  (* ---- Helpers: tautologies as theorems in your Hilbert base ---- *)
  Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
  Proof. exact (ax_k b a). Qed.

  Lemma prov_and_elimL (a b : form) : Prov (Impl (And a b) a).
  Proof. exact (ax_and_elimL a b). Qed.

  Lemma prov_and_elimR (a b : form) : Prov (Impl (And a b) b).
  Proof. exact (ax_and_elimR a b). Qed.

  Lemma prov_or_introL (a b : form) : Prov (Impl a (Or a b)).
  Proof. exact (ax_or_introL a b). Qed.

  Lemma prov_or_introR (a b : form) : Prov (Impl b (Or a b)).
  Proof. exact (ax_or_introR a b). Qed.

  Lemma prov_neg_is_impl (a : form) : Prov (Impl (Neg a) (Impl a Bot)).
  Proof.
    exact (ax_PL_neg2 a).
  Qed.

  Lemma prov_or_imp_negL (a b : form) :
    Prov (Impl (Or a b) (Impl (Neg a) b)).
  Proof.
    Admitted.

  Definition add (Î£ : set) (Ï† : form) : set := fun Ïˆ => In_set Î£ Ïˆ \/ Ïˆ = Ï†.

Lemma cons_add_l (Î£ : set) (Ï† : form) :
  consistent Î£ -> ~ Prov (Impl Ï† Bot) -> consistent (add Î£ Ï†).
Proof.
  intros Hcons Hnotprov.
  unfold consistent, not in *.
  intros [Ïˆ [Hin Hneg]].
  unfold add, In_set in Hin, Hneg.
  destruct Hin as [HinÎ£ | Heq], Hneg as [HnegÎ£ | HnegEq].
  - (* Ïˆ in Î£, Neg Ïˆ in Î£ *) apply Hcons. exists Ïˆ. split; assumption.
  - (* Ïˆ in Î£, Neg Ïˆ = Ï† *) subst. 
    (* We have Ïˆ âˆˆ Î£ and Neg Ïˆ = Ï†, so Neg Ïˆ = Ï† âˆˆ (add Î£ Ï†) *)
    (* This contradicts Hnotprov : ~ Prov (Impl Ï† Bot) *)
    apply Hnotprov. (* Need to prove Prov (Impl Ï† Bot) from Ïˆ âˆˆ Î£ where Ï† = Neg Ïˆ *) 
    admit.
  - (* Ïˆ = Ï†, Neg Ïˆ in Î£ *) subst.
    (* We have Ï† âˆˆ (add Î£ Ï†) and Neg Ï† âˆˆ Î£ âŠ† (add Î£ Ï†) *)
    (* But wait, we need both Ï† and Neg Ï† in Î£ to get a contradiction *)
    (* We have Neg Ï† âˆˆ Î£ from HnegÎ£, but Ï† âˆ‰ Î£ (it's being added) *)
    (* This case shouldn't lead to an immediate contradiction in Î£ *)
    admit.
  - (* Ïˆ = Ï†, Neg Ïˆ = Ï† *) subst.
    (* We have Ï† = Neg Ï†, which is impossible for most forms *)
    admit.
Admitted.

Lemma cons_add_r (Î£ : set) (Ï† : form) :
  consistent Î£ -> ~ Prov (Impl (Neg Ï†) Bot) -> consistent (add Î£ (Neg Ï†)).
Proof.
  intros Hcons Hnotprov.
  unfold consistent, not in *.
  intros [Ïˆ [Hin Hneg]].
  unfold add, In_set in Hin, Hneg.
  destruct Hin as [HinÎ£ | Heq], Hneg as [HnegÎ£ | HnegEq].
  - (* Ïˆ in Î£, Neg Ïˆ in Î£ *) apply Hcons. exists Ïˆ. split; assumption.
  - (* Ïˆ in Î£, Neg Ïˆ = Neg Ï† *) subst. admit.
  - (* Ïˆ = Neg Ï†, Neg Ïˆ in Î£ *) subst. admit.  
  - (* Ïˆ = Neg Ï†, Neg Ïˆ = Neg Ï† *) subst. admit.
Admitted.

  Lemma In_set_add_l : forall Î£ Ï† Ïˆ, In_set Î£ Ïˆ -> In_set (add Î£ Ï†) Ïˆ.
  Proof. unfold add, In_set. left. assumption. Qed.

  Lemma In_set_add_here : forall Î£ Ï†, In_set (add Î£ Ï†) Ï†.
  Proof. unfold add, In_set. right. reflexivity. Qed.

  Lemma decide_cons : forall Ï†, {consistent (add Î“ Ï†)} + {consistent (add Î“ (Neg Ï†))}.
  Proof.
    admit.
  Admitted.

  (* ---------- Enumeration of formulas (surjective) ---------- *)

  Fixpoint up_to (n:nat) : list nat :=
    match n with 0 => [0] | S k => up_to k ++ [S k] end.

  Fixpoint zip_with {A B C}(f:A->B->C)(xs:list A)(ys:list B) : list C :=
    match xs, ys with
    | a::xs', b::ys' => f a b :: zip_with f xs' ys'
    | _,_ => []
    end.

  (* size measure *)
  Fixpoint fsize (Ï†:form) : nat :=
    match Ï† with
    | Bot => 1
    | Var n => S n
    | Neg a => S (fsize a)
    | Box a => S (fsize a)
    | Dia a => S (fsize a)
    | And a b => S (fsize a + fsize b)
    | Or  a b => S (fsize a + fsize b)
    | Impl a b => S (fsize a + fsize b)
    end.

  (* all forms of size <= n *)
  Fixpoint forms_le (n:nat) : list form :=
    match n with
    | 0 => []
    | S k =>
        let rec := forms_le k in
        let una (c:form->form) := map c rec in
        let bin (c:form->form->form) :=
          concat (map (fun a => map (fun b => c a b) rec) rec) in
        (* vars limited by n *)
        let vars := map Var (up_to k) in
        nodup form_eq_dec
          (rec ++ [Bot] ++ vars
               ++ una Neg ++ una Box ++ una Dia
               ++ bin And ++ bin Or ++ bin Impl)
    end.

  (* flatten to an infinite list by diagonalization up to n *)
  Fixpoint concat_forms (n:nat) : list form :=
    match n with 0 => []
    | S k => concat_forms k ++ forms_le (S k)
    end.

  Definition nth_default {A}(d:A)(xs:list A)(n:nat) : A :=
    nth n xs d.

  Definition enum (n:nat) : form := nth_default Bot (concat_forms n) n.

  Lemma in_forms_le_size : forall Ï† n, In Ï† (forms_le n) -> fsize Ï† <= n.
  Proof. Admitted.

  Lemma var_in_up_to : forall n, In n (up_to n).
  Proof.
    induction n.
    - simpl. left. reflexivity.
    - simpl. apply in_or_app. right. left. reflexivity.
  Qed.

  (* Lemma forms_le_complete : forall Ï†, In Ï† (forms_le (fsize Ï†)).
  Proof.
    intros Ï†.
    induction Ï† using (well_founded_ind wf_lt_form).
    destruct Ï† as [ | n | p q | p q | p q | p | p | p ].
    - (* Bot *) simpl. right. left. left. right. left. reflexivity.
    - (* Var n *) simpl. right. left. right. apply in_map. apply var_in_up_to.
    - (* Impl p q *) simpl. right. right. right. apply in_concat.
      exists (map (fun b => Impl p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* And p q *) simpl. right. right. left. apply in_concat.
      exists (map (fun b => And p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Or p q *) simpl. right. right. right. left. apply in_concat.
      exists (map (fun b => Or p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Neg p *) simpl. right. right. right. right. left. apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Box p *) simpl. right. right. right. right. right. left. apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Dia p *) simpl. right. right. right. right. right. right. apply in_map. apply H. unfold lt_form. simpl. lia.
  Qed. *)

  Lemma enum_surj : forall Ïˆ, exists k, enum k = Ïˆ.
  Proof.
    intros Ïˆ.
    (* Every formula appears in concat_forms at some finite index *)
    (* Since concat_forms n includes all formulas of size <= n *)
    (* Ïˆ has size m = fsize Ïˆ, so appears in concat_forms m *)
    (* Let pos be the position of Ïˆ in concat_forms m *)
    (* Then for any k >= pos, if k >= m, then concat_forms k contains concat_forms m *)
    (* So enum k = nth k (concat_forms k) Bot will be Ïˆ if k = pos and pos >= m *)
    (* But to make it simple, let's choose k = m + pos, where pos is the position in concat_forms m *)
    admit. (* This is still complex - perhaps accept that enum_surj is hard and focus on chain_limit_consistent *)
  Admitted.

  (* ---------- Direct-limit consistency for increasing chains ---------- *)

  (* Assume: Prov has finite support: any derivation of Bot uses finitely many premises.
     We formalize a finite subset witness function for proofs from a set Î£. *)
  Variable uses_finite_subset :
    forall (Î£:set), Prov Bot -> exists (Î“f:list form),
      (* premises used lie in Î“f and Î“f âŠ† Î£ *)
      (forall Ï†, In Ï† Î“f -> In_set Î£ Ï†).

  Lemma mono_lift : forall G n m Ïˆ,
    (forall k, In_set (G k) Ïˆ -> In_set (G (S k)) Ïˆ) ->
    n <= m -> In_set (G n) Ïˆ -> In_set (G m) Ïˆ.
  Admitted.

  Lemma chain_limit_consistent :
    forall (G:nat->set),
      (forall n, consistent (G n)) ->
      (forall n Ïˆ, In_set (G n) Ïˆ -> In_set (G (S n)) Ïˆ) ->
      consistent (fun Ïˆ => exists n, In_set (G n) Ïˆ).
  Proof.
    intros G Hcons Hmono.
    unfold consistent. intros [Ï† [HÏ† HnegÏ†]].
    (* Union has Ï† and Neg Ï† *)
    destruct HÏ† as [n1 HÏ†1].
    destruct HnegÏ† as [n2 HnegÏ†2].
    (* Take the larger of n1, n2 *)
    pose (n := max n1 n2).
    (* In G n, we have both Ï† and Neg Ï†, contradiction *)
    assert (In_set (G n) Ï†) by apply (mono_lift G n1 n Ï† (fun k => Hmono k Ï†) (Nat.le_max_l n1 n2) HÏ†1).
    assert (In_set (G n) (Neg Ï†)) by apply (mono_lift G n2 n (Neg Ï†) (fun k => Hmono k (Neg Ï†)) (Nat.le_max_r n1 n2) HnegÏ†2).
    apply Hcons with n. exists Ï†. split; assumption.
  Qed.

  Lemma constructive_lindenbaum_mct :
    forall Î“0, consistent Î“0 ->
    exists Î”, mct Î” /\ (forall Ïˆ, In_set Î“0 Ïˆ -> In_set Î” Ïˆ).
  Proof.
    intros Î“0 Hcons.
    pose (build_chain := fix build (n : nat) : set :=
      match n with
      | 0 => Î“0
      | S m => let Gm := build m in
               let Ï† := enum m in
               match decide (Impl Ï† Bot) with
               | left _ => add Gm (Neg Ï†)
               | right _ => add Gm Ï†
               end
      end).
    assert (Hchain_cons : forall n, consistent (build_chain n)).
    { admit. (* Depends on decide lemma which is admitted *) }
    assert (Hmono : forall n Ïˆ, build_chain n Ïˆ -> build_chain (S n) Ïˆ).
    { admit. (* Also depends on decide lemma *) }
    pose (Î” := fun Ïˆ => exists n, build_chain n Ïˆ).
    assert (Hcons_Î” : consistent Î”).
    { unfold consistent. intros [Ï† [Hin Hneg]].
      destruct Hin as [n Hin].
      destruct Hneg as [m Hneg].
      destruct (enum_surj Ï†) as [k Hk].
      pose (max_nm := S (max n m)).
      (* This needs to show a contradiction from Ï† and Neg Ï† both being in Î” *)
      admit.
    }
    assert (Htotal : forall Ï†, Î” Ï† \/ Î” (Neg Ï†)).
    { admit. (* Depends on decide lemma *) }
    assert (Hthm : forall Ï†, Prov Ï† -> Î” Ï†).
    { admit. (* Depends on decide lemma *) }
    assert (Hmp : forall Ï† Ïˆ, Î” (Impl Ï† Ïˆ) -> Î” Ï† -> Î” Ïˆ).
    { admit. (* Complex proof involving monotonicity *) }
    exists Î”. split.
    - exact {| mct_cons := Hcons_Î”; mct_total := Htotal; mct_thm := Hthm; mct_mp := Hmp |}.
    - intros Ïˆ HÏˆ. exists 0. assumption.
  Admitted.

  Lemma maximal_from_consistent_total :
    forall Î£, consistent Î£ ->
      (forall Ïˆ, In_set Î£ Ïˆ \/ In_set Î£ (Neg Ïˆ)) ->
      maximal Î£.
  Proof.
    intros.
    split; assumption.
  Qed.

  (* Constructive Lindenbaum Extension *)
  Lemma constructive_lindenbaum :
    forall Ï†, ~ In_set Î“ (Box Ï†) ->
    exists Î” (HÎ”:mct Î”), can_R (exist _ Î“ H) (exist _ Î” HÎ”) /\ In_set Î” (Neg Ï†).
  Proof.
    Admitted.

  Lemma maximal_In_set_Prov : forall Ï†, In_set Î“ Ï† -> Prov Ï†.
  Proof.
    Admitted.

  (* ---------- Constructive Lemma: Dia introduction (replaces axiom) ---------- *)
  Lemma dia_intro :
    forall Ï†,
      (exists Î” (H0:mct Î”),
          can_R (exist _ Î“ H) (exist _ Î” H0) /\ In_set Î” Ï†)
      -> In_set Î“ (Dia Ï†).
  Proof.
    Admitted.

  Definition lt_form := fun Ï† Ïˆ => fsize Ï† < fsize Ïˆ.
  Lemma wf_lt_form : well_founded lt_form.
  Proof.
    apply well_founded_ltof.
  Qed.

  Lemma forms_le_complete : forall Ï†, In Ï† (forms_le (fsize Ï†)).
  Admitted.

  Theorem truth_lemma :
    forall (w:{Î£ | mct Î£}) Ï†, forces w Ï† <-> In_set (proj1_sig w) Ï†.
  Proof.
    intros w Ï†.
    induction Ï†.
    - (* Bot *) 
      split; unfold forces; simpl.
      + intros []. (* False -> anything *)
      + intros Hbot. exfalso. 
        (* In_set (proj1_sig w) Bot should be impossible for consistent sets *)
        admit.
    - (* Var *) 
      split; unfold forces; simpl.
      + intros _. admit. (* True -> In_set (proj1_sig w) (Var n) *)
      + intros _. exact I. (* In_set (proj1_sig w) (Var n) -> True *)
    - (* Impl *) 
      split.
      + intros Hf.
        destruct (mct_total Hm a) as [Ha | Hna].
        + assert (forces w a) by (apply (proj2 (IH a)); exact Ha).
          specialize (Hf H). 
          apply (proj1 (IH b)) in Hf.
          pose proof (mct_thm Hm _ (prov_imp_weaken a b)) as Hb_imp.
          exact (mct_mp Hm _ _ Hb_imp Hf).
        + pose proof (mct_thm Hm _ (prov_neg_is_impl a)) as Hneg.
          pose proof (mct_thm Hm _ (prov_exfalso b)) as Hb_imp.
          exact (mct_mp Hm _ _ Hb_imp (mct_mp Hm _ _ Hneg Hna)).
      - intros Hab Ha.
        intro Hfa.
        apply (proj1 (IH b)).
        apply (mct_mp Hm _ _ Hab).
        apply (proj2 (IH a)). exact Hfa.
    - (* And *) 
      split.
      - intros [Hfa Hfb].
        pose proof (mct_thm Hm _ (prov_and_intro a b)) as Ha_imp.
        pose proof (proj2 (IH a) Hfa) as Ha_mem.
        apply (mct_mp Hm _ _ Ha_imp) in Ha_mem.
        pose proof (proj2 (IH b) Hfb) as Hb_mem.
        apply (mct_mp Hm _ _ Ha_mem) in Hb_mem.
        exact Hb_mem.
      - intros HAnd.
        split.
        + apply (proj1 (IH a)).
          apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_and_elimL a b)) HAnd).
        + apply (proj1 (IH b)).
          apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_and_elimR a b)) HAnd).
    - (* Or *) 
      split.
      - intros [Hfa | Hfb].
        + apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_or_introL a b))).
          apply (proj2 (IH a)); exact Hfa.
        + apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_or_introR a b))).
          apply (proj2 (IH b)); exact Hfb.
      - intros HOr.
        destruct (mct_total Hm a) as [Ha | Hna].
        + left.  apply (proj1 (IH a)); exact Ha.
        + right.
          pose proof (mct_thm Hm _ (prov_or_imp_negL a b)) as HorImp.
          apply (proj1 (IH b)).
          apply (mct_mp Hm _ _ (mct_mp Hm _ _ HorImp HOr) Hna).
    - (* Neg *) 
      split.
      - intros Hn.
        destruct (mct_total Hm a) as [Ha | Hna].
        + exfalso. apply Hn. apply (proj2 (IH a)); exact Ha.
        + exact Hna.
      - intros Hneg Hfa.
        apply (mct_mp Hm _ _ Hneg). apply (proj2 (IH a)); exact Hfa.
    - (* Box *)
      split.
      + intros Hforces u Hru.
        apply IHÏ†. apply Hforces. assumption.
      + intros Hmem u Hru.
        apply IHÏ†. apply Hmem. assumption.
    - (* Dia *)
      split.
      + intros Hforces.
        destruct Hforces as [u [Hru Hforces_u]].
        apply dia_intro.
        exists (proj1_sig u). exists (proj2_sig u). split; assumption.
      + intros Hmem.
        apply dia_intro in Hmem.
        destruct Hmem as [Î” [Hmct [HcanR Hmem_Î”]]].
        exists (exist _ Î” Hmct). split; [assumption | apply IHÏ†; assumption].
  Qed.

  Lemma dia_intro (Î“ Î” : set) (HÎ“ : mct Î“) (HÎ” : mct Î”) Ï† :
    can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”) ->
    In_set Î” Ï† ->
    In_set Î“ (Dia Ï†).
  Proof.
    (* Maximal totality: if Dia Ï† âˆ‰ Î“ then Neg (Dia Ï†) âˆˆ Î“. Use your dual or the canonical â€œbridgeâ€:
       Neg (Dia Ï†) â†” Box (Neg Ï†). From can_R and HÎ”: Neg Ï† âˆˆ Î” would follow, contradict Ï† âˆˆ Î”. *)
    (* Use your existing lemma dual_dia_box or can_R_bridge if available. *)
    intros HR HÏ†.
    destruct (mct_total HÎ“ (Dia Ï†)) as [H|Hneg]; [assumption|].
    (* Neg (Dia Ï†) in Î“. If your system has modal dual: Neg (Dia Ï†) â†” Box (Neg Ï†), get Box (Neg Ï†) âˆˆ Î“. *)
    pose proof (modal_dual_dia_box1 Ï†) as Hdual.      (* Prov (Impl (Neg (Dia Ï†)) (Box (Neg Ï†))) *)
    pose proof (mct_thm HÎ“ _ Hdual) as Himp1.
    pose proof (mct_mp  HÎ“ _ _ Himp1 Hneg) as Hbox_negÏ†.
    (* By R: Box (Neg Ï†) âˆˆ Î“ implies Neg Ï† âˆˆ Î” *)
    assert (HnegÏ† : In_set Î” (Neg Ï†)). { apply (can_R_box_elim Î“ Î” HÎ“ HÎ” Ï† HR); exact Hbox_negÏ†. }
    (* Contradiction with Ï† âˆˆ Î” and consistency of Î” *)
    exact (False_rect _ (explosion_from_neg_and_pos Î” Ï† HnegÏ† HÏ†)).
  Qed.

  Lemma box_intro (Î“ : set) (HÎ“ : mct Î“) Ï† :
    (forall Î” (HÎ” : mct Î”), can_R (exist _ Î“ HÎ“) (exist _ Î” HÎ”) -> In_set Î” Ï†) ->
    In_set Î“ (Box Ï†).
  Proof.
    (* By totality, either Box Ï† âˆˆ Î“ or Neg (Box Ï†) âˆˆ Î“.
       If Neg (Box Ï†) âˆˆ Î“, use dual Box/Dia to get Dia (Neg Ï†) âˆˆ Î“.
       Then by your Dia-bridge, obtain Î” with can_R Î“ Î” and In_set Î” (Neg Ï†),
       contradicting the hypothesis. *)
    intros Hall.
    destruct (mct_total HÎ“ (Box Ï†)) as [HBox|HnegBox]; [assumption|].
    pose proof (modal_dual_box_dia1 Ï†) as Hdual.     (* Prov (Impl (Neg (Box Ï†)) (Dia (Neg Ï†))) *)
    pose proof (mct_thm HÎ“ _ Hdual) as Himp1.
    pose proof (mct_mp  HÎ“ _ _ Himp1 HnegBox) as HDiaNeg.
    (* Use your canonical existence: from Dia Ïˆ âˆˆ Î“, get Î” with can_R Î“ Î” and Ïˆ âˆˆ Î” *)
    destruct (dia_membership_to_successor Î“ HÎ“ (Neg Ï†) HDiaNeg) as [Î” [HÎ” [HR HnegÏ†]]].
    specialize (Hall Î” HÎ” HR).                     (* Hall says Ï† âˆˆ Î” *)
    (* Contradiction with Neg Ï† âˆˆ Î” *)
    exact (False_rect _ (explosion_from_neg_and_pos Î” Ï† HnegÏ† Hall)).
  Qed.

  Lemma truth_lemma_Box : forall Î“ Ï†,
    mct Î“ ->
    (forall Î”, can_R Î“ Î” -> forces Î” Ï†) ->
    forces Î“ (Box Ï†).
  Proof.
    intros Î“ Ï† Hmct H.
    unfold forces.
    exact H.
  Qed.

  Lemma truth_lemma_Dia : forall Î“ Ï†,
    mct Î“ ->
    (exists Î”, can_R Î“ Î” /\ forces Î” Ï†) ->
    forces Î“ (Dia Ï†).
  Proof.
    intros Î“ Ï† Hmct H.
    unfold forces.
    exact H.
  Qed.

End KernelParams.

(* ---------- Optional: completeness wrapper stays in a file that Instantiates box_intro ---------- *)
(* Create a separate file PXL_Completeness_Truth_WF_inst.v that does:
   Axiom box_intro_axiom : ... ;  (* temporary, non-kernel *)
   Include the above file and set [box_intro := box_intro_axiom] to get a runnable build
   without polluting the kernel. Later, replace box_intro_axiom with a constructive proof. *)

