Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Canonical.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {SM: Semantics L MD}
        {fsSM: SeparatingSemantics L MD M SM}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Hypothesis H_J: forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi -> (join m1 m2 m <-> context_join (proj1_sig Phi1) (proj1_sig Phi2) (proj1_sig Phi)).

Instance SA
         (LIN_SR: Linderbaum_sepcon_right P):
  SeparationAlgebra (Kworlds M).
Proof.
  constructor.
  + intros.
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    destruct (im_bij _ _ rel m) as [Phi ?].
    erewrite H_J in H |- * by eauto.
    hnf; intros.
    rewrite <- sepcon_comm.
    apply H; auto.
  + intros.
    destruct (im_bij _ _ rel mx) as [Phi_x ?].
    destruct (im_bij _ _ rel my) as [Phi_y ?].
    destruct (im_bij _ _ rel mz) as [Phi_z ?].
    destruct (im_bij _ _ rel mxy) as [Phi_xy ?].
    destruct (im_bij _ _ rel mxyz) as [Phi_xyz ?].
    erewrite H_J in H, H0 by eauto.
    assert (context_join (proj1_sig Phi_x)
             (context_sepcon (proj1_sig Phi_y) (proj1_sig Phi_z)) (proj1_sig Phi_xyz)).
    - hnf; intros x yz ? ?.
      apply context_sepcon_derivable in H7.
      destruct H7 as [y [z [? [? ?]]]].
      rewrite <- H7, sepcon_assoc.
      apply H0; auto.
    - apply LIN_SR in H6.
      destruct H6 as [Phi_yz [? ?]].
      apply context_sepcon_context_join' in H6.
      destruct (su_bij _ _ rel Phi_yz) as [myz ?].
      exists myz.
      erewrite !H_J by eauto.
      auto.
Qed.

Instance uSA
         (DER: at_least_derivable_closed P):
  UpwardsClosedSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  exists m1, m2.
  destruct (im_bij _ _ rel n) as [Psi ?].
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H |- * by eauto.
  erewrite H_R in H0 by eauto.
  do 2 erewrite H_R by eauto.
  split; [| split].
  + rewrite context_join_spec in H by (apply DER, (proj2_sig Phi)).
    rewrite context_join_spec by (apply DER, (proj2_sig Psi)).
    hnf; intros; apply H0, H; auto.
  + hnf; intros; auto.
  + hnf; intros; auto.
Qed.

Instance dSA
         (DER: at_least_derivable_closed P):
  DownwardsClosedSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  exists m.
  destruct (im_bij _ _ rel n1) as [Psi1 ?].
  destruct (im_bij _ _ rel n2) as [Psi2 ?].
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H |- * by eauto.
  erewrite H_R in H0, H1 |- * by eauto.
  split.
  + rewrite context_join_spec in H |- * by (apply DER, (proj2_sig Phi)).
    hnf; intros z ?; apply H; auto.
    destruct H7 as [x [y [? [? ?]]]]; subst.
    exists x, y.
    split; [| split]; auto.
    - eapply deduction_weaken; eauto.
    - eapply deduction_weaken; eauto.
  + hnf; intros; auto.
Qed.

Lemma garbage_collected_canonical_increaing
      {gcsGamma: GarbageCollectSeparationLogic L Gamma}
      (DER: at_least_derivable_closed P):
  IncreasingSeparationAlgebra (Kworlds M).
Proof.
  constructor.
  intros m; hnf; intros n1 n2 ?.
  destruct (im_bij _ _ rel n1) as [Psi1 ?].
  destruct (im_bij _ _ rel n2) as [Psi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_R by eauto.
  erewrite H_J in H by eauto.
  unfold Included, Ensembles.In; intros.
  rewrite derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Psi1)).
  rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Psi2)).
  rewrite <- (sepcon_elim2 TT).
  apply H; auto.
  apply derivable_impp_refl.
Qed.

Lemma ext_canonical_residual
      {ExtSGamma: ExtSeparationLogic L Gamma}
      (LIN_SL: Linderbaum_sepcon_left P):
  ResidualSeparationAlgebra (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  assert (context_join (Union _ empty_context (Singleton _ TT)) (proj1_sig Phi) (proj1_sig Phi)).
  + hnf; intros.
    rewrite deduction_theorem, <- provable_derivable in H0.
    rewrite <- H0, <- sepcon_comm, <- sepcon_ext; auto.
  + apply LIN_SL in H0.
    destruct H0 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    exists n; split.
    - erewrite H_J by eauto.
      auto.
    - erewrite H_R by eauto.
      hnf; intros; auto.
Qed.

Context {s'L: SeparationEmpLanguage L}
        {EmpsGamma: EmpSeparationLogic L Gamma}
        {feSM: EmpSemantics L MD M SM}.

Instance unitSA
         (DER: at_least_derivable_closed P)
         (LIN_SR: Linderbaum_sepcon_right P)
         (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  UnitalSeparationAlgebra (Kworlds M).
Proof.
  intros.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  assert (context_join (proj1_sig Phi) (Union _ empty_context (Singleton _ emp)) (proj1_sig Phi)).
  + hnf; intros.
    rewrite deduction_theorem, <- provable_derivable in H1.
    rewrite <- H1, sepcon_emp; auto.
  + apply LIN_SR in H0.
    destruct H0 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    split; [exists n; split |].
    - apply (@join_comm _ _ (SA LIN_SR)).
      erewrite H_J by eauto.
      auto.
    - erewrite H_R by eauto.
      hnf; intros; auto.
    - clear H1 n Phi H.
      specialize (H0 emp ltac:(right; constructor)).
      unfold Ensembles.In in H0.
      rewrite <- (TRUTH emp) in H0 by eauto.
      rewrite sat_emp in H0; auto.
Qed.

Lemma nonsplit_canonical_split_smaller
      {nssGamma: NonsplitEmpSeparationLogic L Gamma}
      (DER: at_least_derivable_closed P)
      (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  IncreasingSplitSmallerSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H0 by eauto.
  erewrite H_R by eauto.
  unfold Included, Ensembles.In; intros x ?.
  rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)).
  rewrite <- (emp_sepcon_truep_elim x).
  apply deduction_andp_intros.
  + apply H0.
    - rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi1)); auto.
    - apply derivable_impp_refl.
  + rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)).
    rewrite <- (TRUTH emp) by eauto.
    rewrite sat_emp; auto.
Qed.

Lemma dup_canonical_incr_join
      {desGamma: DupEmpSeparationLogic L Gamma}
      (DER: at_least_derivable_closed P)
      (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  IncreasingJoinSelfSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J by eauto.
  intros x y ? ?.
  rewrite <- (andp_elim1 x y).
  rewrite <- (andp_elim2 x y) at 2.
  rewrite <- emp_dup.
  apply deduction_andp_intros; [apply deduction_andp_intros |]; auto.
  rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)); auto.
  rewrite <- (TRUTH emp) by eauto.
  rewrite sat_emp; auto.
Qed.

End Canonical.
