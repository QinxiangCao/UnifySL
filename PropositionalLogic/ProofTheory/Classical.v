Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class ClassicalPropositionalLogic (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {minAX: MinimunAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  excluded_middle: forall x, |-- x || ~~ x
}.

Section Classical.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}.

Lemma derivable_excluded_middle: forall (Phi: context) (x: expr),
  Phi |-- x || ~~ x.
Proof.
  intros.
  pose proof excluded_middle x.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_double_negp_elim: forall (Phi: context) (x: expr),
  Phi |-- ~~ (~~ x) --> x.
Proof.
  intros.
  unfold negp.
  pose proof derivable_orp_elim Phi x (x --> FF) (((x --> FF) --> FF) --> x).
  pose proof derivable_axiom1 Phi x ((x --> FF) --> FF).
  pose proof deduction_modus_ponens _ _ _ H0 H.
  clear H H0.

  pose proof derivable_contradiction_elim Phi (x --> FF) x.
  pose proof deduction_modus_ponens _ _ _ H H1.
  clear H H1.

  pose proof derivable_excluded_middle Phi x.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma double_negp: forall (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_double_negp_elim.
  + apply derivable_double_negp_intros.
Qed.

Lemma deduction_double_negp: forall (Phi: context) (x: expr),
  Phi |-- x <-> Phi |-- ~~ ~~ x.
Proof.
  intros.
  split; intros; eapply deduction_modus_ponens; eauto.
  + apply derivable_double_negp_intros.
  + apply derivable_double_negp_elim.
Qed.

Instance Classical2GodelDummett: GodelDummettPropositionalLogic L Gamma.
Proof.
  constructor.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.
  pose proof derivable_excluded_middle Phi x.
  eapply deduction_modus_ponens; [exact H |].
  apply deduction_orp_elim.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    rewrite deduction_theorem.
    apply derivable_axiom1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros1.
    rewrite deduction_theorem.
    apply deduction_impp_arg_switch.
    apply derivable_contradiction_elim.
Qed.

Lemma contrapositiveNN: forall (x y: expr),
  |-- (~~ y --> ~~ x) --> (x --> y).
Proof.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  rewrite <- deduction_theorem.
  rewrite deduction_double_negp.
  rewrite -> deduction_theorem.
  apply deduction_contrapositivePN.
  apply derivable_assum1.
Qed.

Lemma contrapositiveNP: forall (x y: expr),
  |-- (~~ y --> x) --> (~~ x --> y).
Proof.
  intros.
  rewrite <- (contrapositiveNN (~~ x) y).
  rewrite provable_derivable.
  do 2 rewrite <- deduction_theorem.
  rewrite <- deduction_double_negp.
  do 2 rewrite -> deduction_theorem.
  rewrite <- provable_derivable.
  apply provable_impp_refl.
Qed.

Lemma deduction_contrapositiveNN: forall Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  intros.
  rewrite <- contrapositiveNN.
  auto.
Qed.

Lemma deduction_contrapositiveNP: forall Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  intros.
  rewrite <- contrapositiveNP.
  auto.
Qed.

Lemma impp2orp: forall (x y: expr),
  |-- (x --> y) <--> (~~ x || y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x || ~~ x)); [apply derivable_excluded_middle |].
    apply deduction_orp_elim.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros1.
      apply derivable_assum1.
  + apply deduction_orp_elim.
    - rewrite <- deduction_theorem.
      rewrite <- deduction_theorem.
      apply deduction_falsep_elim.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - apply derivable_axiom1.
Qed.

End Classical.
