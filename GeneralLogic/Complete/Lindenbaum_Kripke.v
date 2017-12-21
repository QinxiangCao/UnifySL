Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.

Section Lindenbaum.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Lemma Linderbaum_suffice: forall (P cP: context -> Prop),
  Countable expr ->
  finite_captured P ->
  subset_preserved P ->
  Lindenbaum_ensures P cP ->
  Lindenbaum_constructable P cP.
Proof.
  intros.
  hnf; intros.
  pose proof Lindenbaum_preserve_omega X _ _ H2 H H0.
  pose proof H1 X Phi H2.
  exists (exist cP (LindenbaumConstruction X Phi P) H4).
  split; auto.
  apply Lindenbaum_included; auto.
Qed.

Lemma Lindenbaum_for_derivable_closed: forall P,
  finite_captured P ->
  subset_preserved P ->
  derivable_subset_preserved P ->
  Lindenbaum_ensures P derivable_closed.
Proof.
  intros; hnf; intros.
  pose proof Lindenbaum_preserve_omega CA _ _ H2 H H0.
  hnf; intros.
  destruct (im_inj _ _ CA x) as [n ?].
  rewrite <- Lindenbaum_pointwise_finite_decided by eauto.
  simpl; right; split; auto.
  eapply H1; [| exact H3].
  unfold Included, Ensembles.In; intros.
  eapply deduction_subst; eauto.
  eapply deduction_weaken; eauto.
  rewrite Union_Included; split.
  + eapply Included_trans; [| apply left_Included_Union].
    apply Lindenbaum_included_n_omega.
  + apply right_Included_Union.
Qed.

End Lindenbaum.
