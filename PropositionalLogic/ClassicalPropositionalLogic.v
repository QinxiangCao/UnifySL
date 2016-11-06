Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.MinimunPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class ClassicalPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {mpGamma: MinimunPropositionalLogic L Gamma} := {
  syntactic_reduction_rule: forall x y, @reduce _ MendelsonReduction x y -> (|-- x <-> |-- y);
  axiom3: forall x y, |-- ((~~ y --> x) --> (~~ y --> ~~ x) --> y);
  true_provable: provable TT
}.

Lemma axiom3_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x.
Proof.
  intros.
  pose proof axiom3 y x.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma contradiction_rule: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- ~~ x ->
  Phi |-- x ->
  Phi |-- y.
Proof.
  intros.
  pose proof axiom3_derivable Phi y x.
  apply (derivable_add_imp_left _ _  (~~ y)) in H.
  apply (derivable_add_imp_left _ _  (~~ y)) in H0.
  pose proof derivable_modus_ponens _ _ _ H0 H1.
  pose proof derivable_modus_ponens _ _ _ H H2.
  auto.
Qed.

Lemma double_negp_add: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ (~~ x) --> x.
Proof.
  intros.
  apply deduction_theorem.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr (~~ (~~ x)))) x (~~ x).
  apply derivable_modus_ponens in H; [| apply derivable_imp_refl].
  apply derivable_modus_ponens in H; [| apply derivable_add_imp_left, derivable_assum; right; constructor].
  auto.
Qed.

Lemma double_negp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  apply deduction_theorem.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr x)) (~~ ~~ x) x.
  apply derivable_modus_ponens in H; [| apply deduction_theorem; apply axiom1_derivable].
  apply derivable_modus_ponens in H; [| apply double_negp_add].
  auto.
Qed.

Lemma contrapositivePP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  intros.
  apply deduction_theorem.
  apply (derivable_weaken1 _ x) in H.
  pose proof derivable_assum1 Phi x.
  apply (derivable_add_imp_left _ _ (~~ y)) in H0.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr x)) y x.
  pose proof derivable_modus_ponens _ _ _ H0 H1.
  pose proof derivable_modus_ponens _ _ _ H H2.
  auto.
Qed.

Lemma contrapositiveNN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  apply derivable_weaken1; eauto.
Qed.

Lemma contrapositiveNP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply deduction_theorem; auto.
Qed.

Lemma contrapositivePN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  apply derivable_weaken1; auto.
Qed.

Lemma assum_exclude_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- ~~ x --> y ->
  Phi |-- x --> y ->
  Phi |-- y.
Proof.
  intros.
  apply contrapositiveNN in H0.
  apply contrapositiveNP in H.
  pose proof axiom3_derivable Phi y x.
  pose proof derivable_modus_ponens _ _ _ H H1.
  pose proof derivable_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma aux_classic_theorem05: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ x --> FF ->
  Phi |-- x.
Proof.
  intros.
  apply contrapositiveNP in H.
  apply (derivable_modus_ponens _ TT x).
  1: rewrite derivable_provable; exists nil; split; [auto | apply true_provable].
  eapply derivable_modus_ponens; eauto.
  rewrite derivable_provable; exists nil; split; [auto |].
  simpl; eapply syntactic_reduction_rule.
  + apply imp_reduce; [| apply reduce_refl].
    apply imp_reduce; [| apply reduce_refl].
    apply neg_reduce.
    apply reduce_step.
    eapply (propag_reduce_spec _ _ _ nil).
    right; right; constructor.
  + simpl; clear H.
    pose proof imp_trans_strong TT (~~ ~~ TT) x.
    eapply modus_ponens; eauto.
    rewrite provable_derivable.
    apply double_negp_elim.
Qed.

Lemma MCS_nonelement_inconsistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x: expr, ~ Phi x <-> Phi |-- x --> FF).
Proof.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 (Union _ Phi (Singleton _ x))).
    unfold consistent in H1.
    rewrite deduction_theorem in H1.
    assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
    assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
    tauto.
  + intro.
    pose proof derivable_assum Phi x H1.
    pose proof derivable_modus_ponens _ _ _ H2 H0.
    destruct H; auto.
Qed.

Lemma MCS_negp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x: expr, Phi (~~ x) <-> ~ Phi x).
Proof.
  intros.
  rewrite MCS_nonelement_inconsistent by auto.
  rewrite MCS_element_derivable by auto.
  split; intros.
  + apply deduction_theorem.
    apply (contradiction_rule _ x).
    - eapply derivable_weaken; eauto.
      intros ? ?; left; auto.
    - apply derivable_assum; right; constructor.
  + eapply derivable_modus_ponens with TT.
    - rewrite derivable_provable; exists nil.
      split; [auto |].
      apply true_provable.
    - apply contrapositivePN.
      eapply derivable_modus_ponens; eauto.
      rewrite derivable_provable; exists nil.
      split; [auto | simpl].
      eapply syntactic_reduction_rule.
      * apply imp_reduce; [| apply reduce_refl].
        apply imp_reduce; [apply reduce_refl |].
        apply reduce_step.
        eapply (propag_reduce_spec _ _ _ nil).
        right; right; constructor.
      * simpl.
        apply imp_refl.
Qed.

Lemma MCS_impp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (derivable_modus_ponens _ x y); auto.
  + assert (~ Phi x \/ Phi y) by tauto.
    clear H0; destruct H1.
    - rewrite <- MCS_negp_iff in H0 by auto.
      rewrite MCS_element_derivable in H0 |- * by auto.
      apply deduction_theorem.
      apply (contradiction_rule _ x).
      * eapply derivable_weaken; eauto.
        intros ? ?; left; auto.
      * apply derivable_assum; right; constructor.
    - rewrite MCS_element_derivable in H0 |- * by auto.
      pose proof axiom1_derivable Phi y x.
      apply (derivable_modus_ponens _ y); auto.
Qed.

Lemma classic_mendelson_consistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}, reduction_consistent_prooftheory MendelsonReduction Gamma.
Proof.
  intros.
  apply reduction_consistent_prooftheory_from_provable; auto.
  hnf; intros.
  apply syntactic_reduction_rule; auto.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance R: SyntacticReduction L := MendelsonReduction.

Inductive provable: expr -> Prop :=
| syntactic_reduction_rule1: forall x y, reduce x y -> provable x -> provable y
| syntactic_reduction_rule2: forall x y, reduce x y -> provable y -> provable x
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y)
| true_provable: provable TT.
(* Elliott Mendelson, Introduction to Mathematical Logic, Second Edition (New York: D. Van Nostrand, 1979) *)

Instance AG: AxiomaticProofTheory.AxiomaticProofTheory L :=
  AxiomaticProofTheory.Build_AxiomaticProofTheory L provable.

Instance G: ProofTheory L := AxiomaticProofTheory.G AG.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance cpG: ClassicalPropositionalLogic L G.
Proof.
  constructor.
  + split.
    - apply syntactic_reduction_rule1; auto. 
    - apply syntactic_reduction_rule2; auto. 
  + apply axiom3.
  + apply true_provable.
Qed.

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

