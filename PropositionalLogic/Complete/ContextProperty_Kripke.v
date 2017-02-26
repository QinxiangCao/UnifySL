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
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Definition orp_witnessed {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x y, Phi (orp x y) -> Phi x \/ Phi y.

Lemma DCS_andp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  rewrite !H0; clear H0; split; intros.
  + pose proof deduction_andp_elim1 Phi x y H.
    pose proof deduction_andp_elim2 Phi x y H.
    auto.
  + destruct H.
    pose proof deduction_andp_intros Phi x y H H0.
    auto.
Qed.

Lemma DCS_orp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  split; intros.
  + apply H0; auto.
  + rewrite !H1 in *.
    destruct H.
    - pose proof deduction_orp_intros1 Phi x y H; auto.
    - pose proof deduction_orp_intros2 Phi x y H; auto.
Qed.

Lemma derivable_closed_union_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi Psi: context) (x: expr),
  derivable_closed Psi ->
  Union _ Phi Psi |-- x ->
  exists y, Psi y /\ Phi |-- y --> x.
Proof.
  intros.
  apply union_derivable in H0.
  destruct H0 as [ys [? ?]].
  revert x H1; induction H0; intros.
  + exists TT.
    split.
    - rewrite derivable_closed_element_derivable by auto.
      unfold truep.
      apply derivable_impp_refl.
    - simpl in H1.
      apply deduction_left_impp_intros; auto.
  + simpl in H2.
    apply (deduction_modus_ponens _ _ (multi_imp l (x --> x0))) in H2.
    Focus 2. {
      apply deduction_weaken0.
      apply provable_multi_imp_arg_switch1.
    } Unfocus.
    specialize (IHForall _ H2); clear H2.
    destruct IHForall as [y [? ?]].
    exists (y && x).
    split.
    - rewrite DCS_andp_iff; auto.
    - eapply deduction_modus_ponens; [eassumption |].
      clear Psi l H H0 H1 H2 H3.
      rewrite <- !deduction_theorem.
      pose proof derivable_assum1 (Union expr Phi (Singleton expr (y --> x --> x0))) (y && x).
      pose proof deduction_andp_elim1 _ _ _ H.
      pose proof deduction_andp_elim2 _ _ _ H.
      eapply deduction_modus_ponens; [exact H1 |].
      eapply deduction_modus_ponens; [exact H0 |].
      apply deduction_weaken1, derivable_assum1.
Qed.

Lemma consistent_spec {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}:
  forall (Phi: context), consistent Phi <-> ~ Phi |-- FF.
Proof.
  intros.
  split; intros.
  + intro.
    destruct H as [x H]; apply H; clear H.
    apply deduction_falsep_elim.
    auto.
  + exists FF; auto.
Qed.

Definition at_least_orp_witnessed
           {L: Language}
           {nL: NormalLanguage L}
           {pL: PropositionalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> orp_witnessed Phi.

