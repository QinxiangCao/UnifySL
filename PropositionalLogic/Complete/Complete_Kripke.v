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
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

(* TODO: delete this file. *)

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Completeness.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kpSM: KripkePropositionalSemantics L MD M SM}
        {kMC: Kmodel -> Prop}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Hypothesis LIN_DER: Linderbaum_derivable P.
Hypothesis DER: at_least_derivable_closed P.
Hypothesis TRUTH: forall x: expr, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x).
Hypothesis CANON: kMC M.

Lemma general_completeness: strongly_complete Gamma SM (KripkeModelClass _ kMC).
Proof.
  intros.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (KripkeModelClass _ kMC) Phi x).
  Focus 2. {
    hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
  } Unfocus.

  intros.
  assert (exists Psi: sig P,
            Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x)
  by (apply LIN_DER in H; auto).
  destruct H0 as [Psi [? ?]].

  intro.
  destruct (su_bij _ _ rel Psi) as [n ?].
  specialize (H2 (KRIPKE: M, n) ltac:(constructor; apply CANON)).
  apply H1; clear H1.

  rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Psi)).
  rewrite <- TRUTH by eauto.
  apply H2; intros.
  rewrite TRUTH by eauto.
  apply H0; auto.
Qed.

End Completeness.
