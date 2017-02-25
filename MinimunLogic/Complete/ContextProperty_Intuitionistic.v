Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.

Local Open Scope logic_base.
Local Open Scope syntax.

Definition derivable_closed {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x, derivable Phi x -> Phi x.

Lemma derivable_closed_element_derivable: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; intros; auto.
  apply derivable_assum; auto.
Qed.

Lemma sig_context_ext: forall {L: Language} (P: context -> Prop) (Phi Psi: sig P),
  (forall x, proj1_sig Phi x <-> proj1_sig Psi x) -> Phi = Psi.
Proof.
  intros.
  pose proof Extensionality_Ensembles _ _ _ (conj (fun x => proj1 (H x)) (fun x => proj2 (H x))).
  destruct Psi as [Psi ?], Phi as [Phi ?].
  simpl in H0; subst.
  pose proof proof_irrelevance _ p p0.
  subst.
  auto.
Qed.

Definition at_least_derivable_closed
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> derivable_closed Phi.

Definition at_least_consistent
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> consistent Phi.

Definition Linderbaum_derivable
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi x, ~ Phi |-- x -> exists Psi: sig P, Included _ Phi (proj1_sig Psi) /\ ~ (proj1_sig Psi) |-- x.
