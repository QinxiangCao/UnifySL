Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {SM: Semantics L MD}
        {tpSM: TrivialPropositionalSemantics L MD SM}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Lemma truth_lemma_falsep (MC: at_least_maximal_consistent P):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= falsep <-> proj1_sig Phi falsep).
Proof.
  intros.
  rewrite sat_falsep.
  pose proof proj2_sig Phi.
  pose proof proj1 (MC _ H0).
  rewrite consistent_spec in H1.
  split; [intros [] |].
  intro; apply H1.
  apply derivable_assum; auto.
Qed.

Lemma truth_lemma_andp
      (MC: at_least_maximal_consistent P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x && y <-> proj1_sig Phi (x && y)).
Proof.
  intros.
  rewrite sat_andp.
  rewrite MCS_andp_iff by (apply MC, (proj2_sig Phi)).
  apply Morphisms_Prop.and_iff_morphism; auto.
Qed.

Lemma truth_lemma_orp
      (MC: at_least_maximal_consistent P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x || y <-> proj1_sig Phi (x || y)).
Proof.
  intros.
  rewrite sat_orp.
  rewrite MCS_orp_iff by (apply MC, (proj2_sig Phi)).
  apply Morphisms_Prop.or_iff_morphism; auto.
Qed.

Lemma truth_lemma_impp
      (MC: at_least_maximal_consistent P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
  rewrite sat_impp.
  rewrite MCS_impp_iff by (apply MC, (proj2_sig Phi)).
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; auto.
Qed.

End TruthLemma.


