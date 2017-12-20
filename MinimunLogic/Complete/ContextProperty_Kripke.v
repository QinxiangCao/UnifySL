Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.ProofTheory.Minimun1.

Local Open Scope logic_base.

Definition derivable_closed {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x, derivable Phi x -> Phi x.

Definition cannot_derive {L: Language} {Gamma: ProofTheory L} (x: expr): context -> Prop :=
  fun Phi => ~ Phi |-- x.

Lemma derivable_closed_element_derivable: forall {L: Language} {Gamma: ProofTheory L} {bSC: BasicSequentCalculus L Gamma} (Phi: context),
  derivable_closed Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; intros; auto.
  apply derivable_assum; auto.
Qed.

