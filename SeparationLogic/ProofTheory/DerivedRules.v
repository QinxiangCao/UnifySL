Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Lemma provable_sepcon_comm_iffp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y: expr),
  |-- x * y <--> y * x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros;
  rewrite <- provable_derivable;
  apply sepcon_comm.
Qed.

Lemma derivable_sepcon_orp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  unfold iffp.
  apply deduction_andp_intros.
  + apply deduction_weaken0.
    apply wand_sepcon_adjoint.
    rewrite provable_derivable.
    apply deduction_orp_elim; apply deduction_weaken0, wand_sepcon_adjoint.
    - apply orp_intros1.
    - apply orp_intros2.
  + apply deduction_orp_elim; apply deduction_weaken0.
    - apply sepcon_mono.
      * apply orp_intros1.
      * apply provable_impp_refl.
    - apply sepcon_mono.
      * apply orp_intros2.
      * apply provable_impp_refl.
Qed.

Lemma provable_sepcon_orp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y z: expr),
  |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_sepcon_orp_left.
Qed.

Lemma derivable_sepcon_orp_right: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  unfold iffp.
  rewrite (sepcon_comm x (y || z)) at 1.
  rewrite <- (sepcon_comm (y || z) x) at 1.
  rewrite <- (sepcon_comm y x) at 1.
  rewrite (sepcon_comm x y) at 1.
  rewrite <- (sepcon_comm z x) at 1.
  rewrite (sepcon_comm x z) at 1.
  apply derivable_sepcon_orp_left.
Qed.

Lemma provable_sepcon_orp_right: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y z: expr),
  |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_sepcon_orp_right.
Qed.

Lemma derivable_sepcon_andp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x && y) * z --> (x * z) && (y * z).
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + rewrite deduction_theorem.
    apply deduction_weaken0.
    apply sepcon_mono.
    - apply andp_elim1.
    - apply provable_impp_refl.
  + rewrite deduction_theorem.
    apply deduction_weaken0.
    apply sepcon_mono.
    - apply andp_elim2.
    - apply provable_impp_refl.
Qed.

Lemma provable_sepcon_andp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y z: expr),
  |-- (x && y) * z --> (x * z) && (y * z).
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_sepcon_andp_left.
Qed.

Lemma derivable_sepcon_andp_right: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x * (y && z) --> (x * y) && (x * z).
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + rewrite deduction_theorem.
    apply deduction_weaken0.
    apply sepcon_mono.
    - apply provable_impp_refl.
    - apply andp_elim1.
  + rewrite deduction_theorem.
    apply deduction_weaken0.
    apply sepcon_mono.
    - apply provable_impp_refl.
    - apply andp_elim2.
Qed.

Lemma provable_sepcon_andp_right: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y z: expr),
  |-- x * (y && z) --> (x * y) && (x * z).
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_sepcon_andp_right.
Qed.

Lemma provable_FF_sepcon: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x: expr),
  |-- FF * x --> FF.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  apply falsep_elim.
Qed.

Lemma derivable_FF_sepcon: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- FF * x --> FF.
Proof.
  intros.
  apply deduction_weaken0.
  apply provable_FF_sepcon.
Qed.

Lemma provable_sepcon_FF: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x: expr),
  |-- x * FF --> FF.
Proof.
  intros.
  rewrite (sepcon_comm x FF).
  apply provable_FF_sepcon.
Qed.

Lemma derivable_sepcon_FF: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x * FF --> FF.
Proof.
  intros.
  rewrite (sepcon_comm x FF).
  apply derivable_FF_sepcon.
Qed.

Lemma provable_wand_sepcon_modus_ponens1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y: expr),
  |-- (x -* y) * x --> y.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  apply provable_impp_refl.
Qed.

Lemma provable_wand_sepcon_modus_ponens2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (x y: expr),
  |-- x * (x -* y) --> y.
Proof.
  intros.
  rewrite (sepcon_comm x (x -* y)).
  apply provable_wand_sepcon_modus_ponens1.
Qed.

Lemma derivable_emp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpsGamma: EmpSeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- emp.
Proof.
  intros.
  pose proof derivable_sepcon_elim2 Phi TT emp.
  pose proof derivable_sepcon_emp Phi TT.
  apply deduction_andp_elim2 in H0.
  pose proof derivable_impp_refl Phi FF.
  pose proof deduction_modus_ponens _ _ _ H1 H0.
  pose proof deduction_modus_ponens _ _ _ H2 H.
  auto.
Qed.

Lemma GC_Classical_collapse_aux: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpsGamma: EmpSeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x --> x * x.
Proof.
  intros.
  pose proof derivable_sepcon_emp Phi x.
  apply deduction_andp_elim2 in H.
  eapply deduction_impp_trans;
    [exact H | eapply deduction_impp_trans with (x * (x || ~~ x))]; clear H.
  + apply deduction_weaken0.
    apply sepcon_mono; [apply provable_impp_refl |].
    rewrite provable_derivable.
    rewrite <- deduction_theorem.
    apply derivable_excluded_middle.
  + eapply deduction_impp_trans.
    - eapply deduction_andp_elim1.
      apply derivable_sepcon_orp_right.
    - apply deduction_orp_elim; [apply derivable_impp_refl |].
      rewrite <- deduction_theorem.
      pose proof derivable_assum1 Phi (x * (~~ x)).
      pose proof deduction_sepcon_elim1 _ _ _ H.
      pose proof deduction_sepcon_elim2 _ _ _ H.
      eapply deduction_contradiction_elim; [exact H0 | exact H1].
Qed.

Theorem GC_Classical_collapse: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpsGamma: EmpSeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr),
  |-- x * y <--> x && y.
Proof.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context); clearbody Phi.
  unfold iffp.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - rewrite deduction_theorem.
      apply derivable_sepcon_elim1.
    - rewrite deduction_theorem.
      apply derivable_sepcon_elim2.
  + eapply deduction_impp_trans.
    - apply GC_Classical_collapse_aux.
    - apply deduction_weaken0.
      apply sepcon_mono.
      * apply andp_elim1.
      * apply andp_elim2.
Qed.
