Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {AX: NormalAxiomatization L Gamma}.

Lemma can_derive_finite_witnessed: forall x,
  finite_witnessed (can_derive x).
Proof.
  intros.
  unfold can_derive.
  hnf; intros.
  rewrite derivable_provable in H.
  destruct H as [xs [? ?]].
  exists xs.
  split; auto.
  rewrite derivable_provable.
  exists xs.
  split; auto.
  rewrite Forall_forall; auto.
Qed.

Lemma cannot_derive_finite_captured: forall x,
  finite_captured (cannot_derive x).
Proof.
  intros.
  apply (not_finite_witnessed_finite_captured _ (can_derive_finite_witnessed x)).
Qed.

End ContextProperty.