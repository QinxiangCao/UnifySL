Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  sepcon_comm: forall x y, |-- x * y --> y * x;
  sepcon_assoc: forall x y z, |-- x * (y * z) <--> (x * y) * z;
  wand_sepcon_adjoint: forall x y z, |-- x * y --> z <-> |-- x --> (y -* z);
  sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2)
}.

Class EmpSeparationLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} := {
  sepcon_emp: forall x, |-- x * emp <--> x
}.

Class ExtSeparationLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} := {
  sepcon_ext: forall x, |-- x --> x * TT
}.

Class GarbageCollectSeparationLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} := {
  sepcon_elim1: forall x y, |-- x * y --> x
}.

Lemma derivable_sepcon_comm: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y --> y * x.
Proof.
  intros.
  pose proof sepcon_comm x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_sepcon_assoc: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  pose proof sepcon_assoc x y z.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_sepcon_emp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpsGamma: EmpSeparationLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x * emp <--> x.
Proof.
  intros.
  pose proof sepcon_emp x.
  apply deduction_weaken0; auto.
Qed.

Lemma deduction_sepcon_comm: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y <-> Phi |-- y * x.
Proof.
  intros.
  pose proof derivable_sepcon_comm Phi x y.
  pose proof derivable_sepcon_comm Phi y x.
  split; intros; eapply deduction_modus_ponens; eauto.
Qed.

Lemma deduction_sepcon_assoc: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x * (y * z) <-> Phi |-- (x * y) * z.
Proof.
  intros.
  pose proof derivable_sepcon_assoc Phi x y z.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  split; intros; eapply deduction_modus_ponens; eauto.
Qed.

Lemma derivable_sepcon_elim1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y --> x.
Proof.
  intros.
  pose proof sepcon_elim1 x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_sepcon_elim2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y --> y.
Proof.
  intros.
  intros.
  pose proof derivable_sepcon_elim1 Phi y x.
  eapply deduction_impp_trans; eauto.
  apply deduction_weaken0.
  apply sepcon_comm.
Qed.

Lemma deduction_sepcon_elim1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y ->
  Phi |-- x.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_sepcon_elim1.
Qed.

Lemma deduction_sepcon_elim2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x * y ->
  Phi |-- y.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_sepcon_elim2.
Qed.

