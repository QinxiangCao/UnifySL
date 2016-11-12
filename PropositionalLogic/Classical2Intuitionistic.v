Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition ClassicalImpAndOrAsPrimeReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {mcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable ImpAndOrAsPrime.atomic_reduce Gamma.
Proof.
  hnf; intros.
  destruct H; split.
  + rewrite provable_derivable.
    rewrite <- !deduction_theorem.
    apply (contradiction_rule _ x); apply derivable_assum.
    - left; right; constructor.
    - right; constructor.
  + pose proof axiom3 TT (~~ x).
    pose proof true_provable.
    pose proof add_imp_left _ (~~ ~~ x) H0.
    pose proof modus_ponens _ _ H H1.
    eapply provable_reduce with ((x --> ~~ TT) --> ~~ x).
    Focus 1. {
      apply imp_reduce; [| apply reduce_refl].
      apply imp_reduce; [apply reduce_refl |].
      apply reduce_step.
      right; right; constructor.
    } Unfocus.
    eapply imp_trans; [| exact H2].
    pose proof imp_trans_strong (~~ ~~ x) x (~~ TT).
    eapply modus_ponens; [exact H3 |].
    rewrite provable_derivable.
    apply double_negp_add.
Qed.

Definition ClassicalIffReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {mcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable ReduceIff.atomic_reduce Gamma.
Proof.
  hnf; intros.
  split; apply (fun H => proj2 (provable_reduce _ (y --> y) H)).
  + apply imp_reduce; [| apply reduce_refl].
    apply reduce_step; right; left; auto.
  + apply imp_refl.
  + apply imp_reduce; [apply reduce_refl |].
    apply reduce_step; right; left; auto.
  + apply imp_refl.
Qed.

Definition ClassicalTrueReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {mcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable ReduceTrue.atomic_reduce Gamma.
Proof.
  hnf; intros.
  destruct H.
  split.
  + apply add_imp_left.
    apply imp_refl.
  + apply add_imp_left.
    apply true_provable.
Qed.

Definition ClassicalPropositionalPropagationReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {mcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  PropositonalPropagationConsistentProvable Gamma.
Proof.
  hnf; intros.
  destruct H; destruct H0.
  + rewrite !imp1_propag_denote.
Admitted.

Module ClassicalPropositionalLogic2Intuitionistic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance R: SyntacticReduction L := MendelsonReduction.
Instance G: ProofTheory L := ClassicalPropositionalLogic.G Var.
Instance nG: NormalProofTheory L G := ClassicalPropositionalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := ClassicalPropositionalLogic.mpG Var.
Instance mcG: ReductionConsistentProofTheory MendelsonReduction G := ClassicalPropositionalLogic.mcG Var.
Instance cpG: ClassicalPropositionalLogic L G := ClassicalPropositionalLogic.cpG Var.

Instance icG: ReductionConsistentProofTheory IntuitionisticReduction G.
  apply Build3_ReductionConsistentProofTheory.
  + simpl.
    repeat apply disjunction_reduce_consistent_provable.
    - apply ClassicalImpAndOrAsPrimeReduction.
    - apply ClassicalIffReduction.
    - apply ClassicalTrueReduction.
  + apply PropositionalLanguage.RPPC_RPC.
    apply ClassicalPropositionalPropagationReduction.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Admitted.
(*
Definition ClassicalIntuitionisticReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {rcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  ReductionConsistentProofTheory IntuitionisticReduction Gamma.
Proof.
  apply Build3_ReductionConsistentProofTheory.
  + simpl.
    repeat apply disjunction_reduce_consistent_provable.
    - apply ClassicalImpAndOrAsPrimeReduction.
    - apply ClassicalIffReduction.
    - apply ClassicalTrueReduction.
  + hnf; intros.
    destruct sp; simpl.
Abort.

*)
End ClassicalPropositionalLogic2Intuitionistic.