Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}
        {Gamma: ProofTheory L}.

Definition derivable_closed : context -> Prop :=
  fun Phi => forall x, derivable Phi x -> Phi x.

Definition can_derive (x: expr): context -> Prop :=
  fun Phi => Phi |-- x.

Definition cannot_derive (x: expr): context -> Prop :=
  fun Phi => ~ Phi |-- x.

Context {bSC: BasicSequentCalculus L Gamma}.

Lemma derivable_closed_element_derivable: forall (Phi: context),
  derivable_closed Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; intros; auto.
  apply derivable_assum; auto.
Qed.

Lemma can_derive_superset_preserved: forall x,
  superset_preserved (can_derive x).
Proof.
  intros.
  unfold can_derive.
  hnf; intros.
  eapply deduction_weaken; eauto.
Qed.

Lemma cannot_derive_subset_preserved: forall x,
  subset_preserved (cannot_derive x).
Proof.
  intros.
  apply (not_superset_preserved_subset_preserved _ (can_derive_superset_preserved x)).
Qed.

End ContextProperty.