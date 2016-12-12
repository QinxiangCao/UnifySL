Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.PropositionalLogic.Complete_Kripke.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics. Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.SeparationLogic.SeparationLogic.
Require Import Logic.SeparationLogic.SoundCompleteParameter.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Canonical_All.

Context (Var: Type).
Context (CV: Countable Var).
Context (SLP: SL_Parameter).

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance G: ProofTheory L := SeparationLogic.G Var SLP.
Instance nG: NormalProofTheory L G := SeparationLogic.nG Var SLP.
Instance mpG: MinimunPropositionalLogic L G := SeparationLogic.mpG Var SLP.
Instance ipG: IntuitionisticPropositionalLogic L G := SeparationLogic.ipG Var SLP.
Instance MD: Model := FlatSemanticsModel.MD Var.
Instance kMD: KripkeModel MD := FlatSemanticsModel.kMD Var.
Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M):= FlatSemanticsModel.kiM (FlatSemanticsModel.underlying_frame Var M).
Instance J (M: Kmodel): Join (Kworlds M):= FlatSemanticsModel.J (FlatSemanticsModel.underlying_frame Var M).
Instance SA (M: Kmodel): SeparationAlgebra (Kworlds M):= FlatSemanticsModel.SA (FlatSemanticsModel.underlying_frame Var M).
Instance dSA (M: Kmodel): DownwardsClosedSeparationAlgebra (Kworlds M):= FlatSemanticsModel.dSA (FlatSemanticsModel.underlying_frame Var M).
Instance uSA (M: Kmodel): UpwardsClosedSeparationAlgebra (Kworlds M):= FlatSemanticsModel.uSA (FlatSemanticsModel.underlying_frame Var M).

Instance SM: Semantics L MD := FlatSemanticsModel.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := FlatSemanticsModel.kiSM Var M.
Instance fsSM (M: Kmodel): FlatSemantics.FlatSemantics L MD M SM := FlatSemanticsModel.fsSM Var M.
Instance UsSM (M: Kmodel): UnitarySemantics L MD M SM := FlatSemanticsModel.UsSM Var M.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Var Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV _ (canonical_model_canonical Var)).
  + intros.
    hnf in H; unfold id in H; subst Phi0.
    reflexivity.
  + reflexivity.
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM (AllModel _).
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (AllModel _) Phi x).
  + intros.
    assert (exists Psi: DCS Var G, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply (Lindenbaum_lemma Var CV) in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Var Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; intros; [hnf; auto |].
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_All.

End Canonical_All.
