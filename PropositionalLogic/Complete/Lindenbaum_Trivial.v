Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section Lindenbaum_Trivial.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.

Lemma Lindenbaum_for_max_consistent: forall P,
  Lindenbaum_preserves P ->
  context_orp_captured P ->
  at_least consistent P ->
  derivable_subset_preserved P ->
  Lindenbaum_ensures P (maximal consistent).
Proof.
  intros.
  pose proof derivable_subset_preserved_subset_preserved _ H2.
  pose proof Lindenbaum_for_derivable_closed _ H H2.
  pose proof Lindenbaum_for_orp_witnessed _ H H3 H0 H4.
  pose proof Lindenbaum_for_consistent _ H H1.
  hnf; intros.
  apply DDCS_MCS.
  + apply H4; auto.
  + apply H5; auto.
  + apply H6; auto.
Qed.

Lemma Lindenbaum_consistent_ensures_max_consistent {AX: NormalAxiomatization L Gamma}: Lindenbaum_ensures consistent (maximal consistent).
Proof.
  intros.
  apply Lindenbaum_for_max_consistent.
  - apply Lindenbaum_preserves_cannot_derivable.
  - unfold cannot_derive.
    hnf; intros.
    exists x; auto.
Qed.


End Lindenbaum_Trivial.
