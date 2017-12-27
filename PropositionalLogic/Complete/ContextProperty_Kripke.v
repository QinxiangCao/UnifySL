Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section ContextPropertu.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}.

Definition orp_witnessed: context -> Prop :=
  fun Phi => forall x y, Phi (orp x y) -> Phi x \/ Phi y.

Context {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.

Lemma DCS_truep: forall (Phi: context),
  derivable_closed Phi ->
  Phi TT.
Proof.
  intros.
  apply H.
  apply derivable_impp_refl.
Qed.

Lemma DCS_andp_iff: forall (Phi: context),
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

Lemma DCS_multi_and_iff: forall (Phi: context),
  derivable_closed Phi ->
  (forall xs: list expr, Phi (multi_and xs) <-> Forall Phi xs).
Proof.
  intros.
  unfold multi_and.
  pose proof fold_left_rev_right (fun x y => y && x) xs TT.
  simpl in H0.
  change (fun x y => x && y) with andp in H0.
  rewrite <- H0.
  clear H0.
  rewrite <- Forall_rev.
  generalize (rev xs) as ys; clear xs.
  induction ys.
  + split; intros.
    - constructor.
    - simpl.
      apply DCS_truep; auto.
  + simpl.
    rewrite DCS_andp_iff by auto.
    rewrite IHys.
    clear.
    split; intros.
    - constructor; tauto.
    - inversion H; auto.
Qed.

Lemma DCS_orp_iff: forall (Phi: context),
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

Existing Instance SequentCalculus2Axiomatization_minAX.
Existing Instance SequentCalculus2Axiomatization_ipGamma.

Lemma derivable_closed_union_derivable {AX: NormalAxiomatization L Gamma}: forall (Phi Psi: context) (x: expr),
  derivable_closed Psi ->
  Union _ Phi Psi |-- x ->
  exists y, Psi y /\ Phi |-- y --> x.
Proof.
  intros.
  rewrite derivable_provable in H0.
  destruct H0 as [xs [? ?]].
  pose proof provable_multi_imp_split _ _ _ _ H0 H1 as [xs1 [xs2 [? [? ?]]]].
  pose proof H4.
  apply multi_and_multi_imp in H4.
  eapply modus_ponens in H4; [| apply provable_multi_imp_arg_switch1].
  exists (multi_and xs2).
  split.
  + apply DCS_multi_and_iff; auto.
  + rewrite derivable_provable.
    exists xs1.
    split; auto.
    eapply modus_ponens.
    - apply provable_multi_imp_weaken.
      rewrite <- multi_and_multi_imp.
    SearchAbout multi_imp.


  apply multi_and_multi_imp in H4.
  
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

Lemma consistent_spec:
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

