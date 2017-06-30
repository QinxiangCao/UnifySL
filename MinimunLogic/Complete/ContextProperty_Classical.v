Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.

Definition maximal_consistent {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => consistent Phi /\ forall Psi, consistent Psi -> Included _ Phi Psi -> Included _ Psi Phi.

Lemma maximal_consistent_spec {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}:
  forall Phi, maximal_consistent Phi <-> consistent Phi /\ forall x, consistent (Union _ Phi (Singleton _ x)) -> Phi x.
Proof.
  intros.
  split; intros [? ?]; split; auto.
  + intros.
    specialize (H0 _ H1).
    specialize (H0 (fun x H => Union_introl _ _ _ _ H)).
    specialize (H0 x).
    apply H0; right; constructor.
  + intros.
    hnf; intros.
    apply H0.
    unfold consistent in*.
    destruct H1 as [y ?].
    exists y.
    intro; apply H1.
    eapply deduction_weaken; [| exact H4].
    intros ? [? | ?]; auto.
    destruct H5; auto.
Qed.

Lemma maximal_consistent_derivable_closed: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  derivable_closed Phi.
Proof.
  intros.
  hnf; intros.
  assert (consistent (Union _ Phi (Singleton _ x))).
  Focus 1. {
    destruct H as [[y ?] _].
    exists y.
    intro.
    pose proof deduction_impp_intros _ _ _ H1.
    pose proof deduction_modus_ponens _ _ _ H0 H2.
    auto.
  } Unfocus.
  destruct H.
  specialize (H2 _ H1).
  specialize (H2 (fun x H => Union_introl _ _ _ x H)).
  apply H2.
  right; constructor.
Qed.

Lemma MCS_element_derivable: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  apply derivable_closed_element_derivable, maximal_consistent_derivable_closed.
  auto.
Qed.

Definition at_least_maximal_consistent
           {L: Language}
           {nL: NormalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> maximal_consistent Phi.

Definition Linderbaum_consistent
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, consistent Phi -> exists Psi: sig P, Included _ Phi (proj1_sig Psi).
