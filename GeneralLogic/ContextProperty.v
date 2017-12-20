Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Definition at_least {L: Language} (P cP: context -> Prop): Prop :=
  forall (Phi: context), cP Phi -> P Phi.

Definition maximal {L: Language} (P: context -> Prop): context -> Prop :=
  fun Phi => P Phi /\ forall Psi, P Psi -> Included _ Phi Psi -> Included _ Psi Phi.

Definition Linderbaum_constructable
           {L: Language}
           {Gamma: ProofTheory L}
           (P cP: context -> Prop): Prop :=
  forall Phi, P Phi -> exists Psi: sig cP, Included _ Phi (proj1_sig Psi) /\ P (proj1_sig Psi).
  
Lemma sig_context_ext: forall {L: Language} (cP: context -> Prop) (Phi Psi: sig cP),
  (forall x, proj1_sig Phi x <-> proj1_sig Psi x) -> Phi = Psi.
Proof.
  intros.
  pose proof Extensionality_Ensembles _ _ _ (conj (fun x => proj1 (H x)) (fun x => proj2 (H x))).
  destruct Psi as [Psi ?], Phi as [Phi ?].
  simpl in H0; subst.
  pose proof proof_irrelevance _ c c0.
  subst.
  auto.
Qed.

