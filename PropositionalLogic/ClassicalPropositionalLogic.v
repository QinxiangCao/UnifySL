Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class ClassicalPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  excluded_middle: forall x, |-- x || (x --> FF)
}.

Lemma excluded_middle_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x || (x --> FF).
Proof.
  intros.
  pose proof excluded_middle x.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma double_negp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  unfold negp.
  apply derivable_weaken0.
  apply aux_minimun_theorem02.
Qed.

Lemma double_negp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ (~~ x) --> x.
Proof.
  intros.
  apply derivable_weaken0.
  unfold negp.
  pose proof orp_elim x (x --> FF) (((x --> FF) --> FF) --> x).
  pose proof axiom1 x ((x --> FF) --> FF).
  pose proof modus_ponens _ _ H H0.
  clear H H0.

  pose proof aux_minimun_theorem02 (x --> FF) FF.
  pose proof falsep_elim x.
  pose proof remove_iden_assum_from_imp _ _ ((x --> FF) --> FF) H0.
  pose proof remove_iden_assum_from_imp _ _ (x --> FF) H2.
  pose proof modus_ponens _ _ H3 H.
  pose proof modus_ponens _ _ H1 H4.
  clear H1 H H0 H2 H3 H4.

  pose proof excluded_middle x.
  pose proof modus_ponens _ _ H5 H.
  auto.
Qed.

Lemma double_negp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <-> Phi |-- ~~ ~~ x.
Proof.
  intros.
  split; intros; eapply derivable_modus_ponens; eauto.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

(*
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

Lemma aux_classic_theorem05: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {mcGamma: ReductionConsistentProofTheory MendelsonReduction Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ x --> FF ->
  Phi |-- x.
Proof.
  intros.
  apply contrapositiveNP in H.
  apply (derivable_modus_ponens _ TT x).
  1: rewrite derivable_provable; exists nil; split; [auto | apply true_provable].
  eapply derivable_modus_ponens; eauto.
  rewrite derivable_provable; exists nil; split; [auto |].
  simpl; eapply provable_reduce.
  + apply imp_reduce; [| apply reduce_refl].
    apply imp_reduce; [| apply reduce_refl].
    apply neg_reduce.
    apply reduce_step.
    right; right; constructor.
  + simpl; clear H.
    pose proof imp_trans_strong TT (~~ ~~ TT) x.
    eapply modus_ponens; eauto.
    rewrite provable_derivable.
    apply double_negp_elim.
Qed.
*)

Lemma classical_derivable_spec: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <-> ~ consistent (Union _ Phi (Singleton _ (~~ x))).
Proof.
  intros.
  rewrite double_negp.
  unfold negp at 1.
  rewrite <- deduction_theorem.
  unfold consistent.
  tauto.
Qed.

Lemma MCS_nonelement_inconsistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
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

Lemma MCS_andp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  apply maximal_consistent_derivable_closed in H.
  apply DCS_andp_iff; auto.
Qed.

Lemma MCS_orp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  split; intros.
  + destruct (Classical_Prop.classic (Phi x)); auto.
    destruct (Classical_Prop.classic (Phi y)); auto.
    exfalso.
    rewrite MCS_nonelement_inconsistent in H1 by auto.
    rewrite MCS_nonelement_inconsistent in H2 by auto.
    rewrite MCS_element_derivable in H0 by auto.
    pose proof orp_elim_derivable Phi x y FF.
    pose proof derivable_modus_ponens _ _ _ H1 H3.
    pose proof derivable_modus_ponens _ _ _ H2 H4.
    pose proof derivable_modus_ponens _ _ _ H0 H5.
    destruct H.
    auto.
  + destruct H0; rewrite MCS_element_derivable in H0 |- * by auto.
    - pose proof orp_intros1_derivable Phi x y.
      pose proof derivable_modus_ponens _ _ _ H0 H1.
      auto.
    - pose proof orp_intros2_derivable Phi x y.
      pose proof derivable_modus_ponens _ _ _ H0 H1.
      auto.
Qed.

Lemma MCS_impp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (derivable_modus_ponens _ x y); auto.
  + pose proof excluded_middle_derivable Phi y.
    rewrite <- MCS_element_derivable in H1 by auto.
    rewrite MCS_orp_iff in H1 by auto.
    pose proof excluded_middle_derivable Phi x.
    rewrite <- MCS_element_derivable in H2 by auto.
    rewrite MCS_orp_iff in H2 by auto.
    destruct H1; [| destruct H2].
    - rewrite MCS_element_derivable in H1 |- * by auto.
      apply derivable_add_imp_left; auto.
    - exfalso.
      apply H0 in H2.
      rewrite MCS_element_derivable in H1, H2 by auto.
      pose proof derivable_modus_ponens _ _ _ H2 H1.
      destruct H; auto.
    - rewrite MCS_element_derivable in H2 |- * by auto.
      rewrite <- deduction_theorem in H2 |- *.
      eapply derivable_modus_ponens; [exact H2 |].
      apply falsep_elim_derivable.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| excluded_middle: forall x, provable (x || (x --> FF)).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance cpG: ClassicalPropositionalLogic L G.
Proof.
  constructor.
  apply excluded_middle.
Qed.

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

