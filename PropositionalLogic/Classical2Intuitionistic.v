Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.MinimunPropositionalLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition ClassicalImpAndOrAsPrimeReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {rcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable ImpAndOrAsPrime.atomic_reduce Gamma.
Proof.
  hnf; intros.
  destruct H.
  +
Abort.

Definition ClassicalIntuitionisticReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {rcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  ReductionConsistentProofTheory IntuitionisticReduction Gamma.
Proof.
  apply Build2_ReductionConsistentProofTheory.
  + simpl.
    repeat apply disjunction_reduce_consistent_provable.
Abort.

