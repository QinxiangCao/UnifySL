Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class DeMorganPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  weak_excluded_middle: forall x, |-- ~~ x || ~~ ~~ x
}.

Lemma derivable_weak_excluded_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {dmpGamma: DeMorganPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ x || ~~ ~~ x.
Proof.
  intros.
  pose proof weak_excluded_middle x.
  apply deduction_weaken0; auto.
Qed.

Lemma demorgan_negp_andp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {dmpGamma: DeMorganPropositionalLogic L Gamma} (x y: expr),
  |-- ~~ (x && y) <--> (~~ x || ~~ y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros; [| rewrite <- provable_derivable; apply demorgan_orp_negp].
  rewrite <- deduction_theorem.
  apply (deduction_modus_ponens _ (~~ x || ~~ ~~ x)); [apply derivable_weak_excluded_middle |].
  apply deduction_orp_elim.
  + apply deduction_weaken0.
    apply orp_intros1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    unfold negp at 4.
    rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x --> FF)).
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ (x && y)).
      * apply deduction_andp_intros; [| apply deduction_weaken1]; apply derivable_assum1.
      * do 3 apply deduction_weaken1; apply derivable_assum1.
    - apply deduction_weaken1; apply derivable_assum1.
Qed.

