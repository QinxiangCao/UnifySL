Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.

Local Open Scope logic_base.
Local Open Scope syntax.

Class MinimunPropositionalLogic (L: Language) {nL: NormalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} := {
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
}.



Lemma union_derivable {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall (Phi1 Phi2: context) (x: expr),
    Union _ Phi1 Phi2 |-- x <->
    exists xs, Forall Phi2 xs /\ Phi1 |-- multi_imp xs x.
Proof.
  intros.
  split; intros.
  + rewrite derivable_provable in H.
    destruct H as [xs [? ?]].
    pose proof provable_multi_imp_split _ _ _ _ H H0.
    destruct H1 as [xs1 [xs2 [? [? ?]]]].
    exists xs2.
    split; auto.
    rewrite derivable_provable.
    exists xs1; auto.
  + destruct H as [xs2 [? ?]].
    rewrite derivable_provable in H0.
    destruct H0 as [xs1 [? ?]].
    unfold multi_imp in H1.
    rewrite <- fold_right_app in H1.
    fold (multi_imp (xs1 ++ xs2) x) in H1.
    rewrite derivable_provable.
    exists (xs1 ++ xs2).
    split; auto.
    rewrite Forall_app_iff; split;
    eapply Forall_impl; try eassumption.
    - intros; left; auto.
    - intros; right; auto.
Qed.



Lemma derivable_assum1: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Union _ Phi (Singleton _ x) |-- x.
Proof.
  intros.
  apply derivable_assum.
  right; constructor.
Qed.

Ltac solve_assum :=
  (first [apply derivable_assum1 | assumption | apply deduction_weaken1; solve_assum] || fail 1000 "Cannot find the conclusion in assumption").


Theorem deduction_theorem {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply deduction_impp_intros; auto.
  + apply deduction_impp_elim; auto.
Qed.


Lemma derivable_impp_refl: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma deduction_left_impp_intros: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma derivable_axiom1: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> y --> x.
Proof.
  intros.
  apply deduction_weaken0, axiom1.
Qed.

Lemma derivable_axiom2: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  apply deduction_weaken0, axiom2.
Qed.

Lemma derivable_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> (x --> y) --> y.
Proof.
  intros.
  apply deduction_weaken0, aux_minimun_theorem02.
Qed.

Lemma deduction_impp_trans: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x --> y ->
  Phi |-- y --> z ->
  Phi |-- x --> z.
Proof.
  intros.
  pose proof provable_impp_trans x y z.
  apply (deduction_weaken0 Phi) in H1.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma derivable_impp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  apply deduction_weaken0, provable_impp_arg_switch.
Qed.

Lemma deduction_impp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x --> y --> z ->
  Phi |-- y --> x --> z.
Proof.
  intros.
  eapply deduction_modus_ponens; [exact H |].
  apply derivable_impp_arg_switch.
Qed.
