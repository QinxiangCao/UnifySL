Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.GodelDummettLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.

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

Class UnitarySeparationLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {usL: UnitarySeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} := {
  sepcon_emp: forall x, |-- x * emp <--> x
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

Lemma derivable_sepcon_emp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {usL: UnitarySeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {usGamma: UnitarySeparationLogic L Gamma} (Phi: context) (x: expr),
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

Instance sepcon_proper {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply sepcon_mono; auto.
Qed.

Instance wand_proper {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  apply wand_sepcon_adjoint.
  rewrite provable_derivable in H0 |- *.
  eapply deduction_impp_trans; [clear H0 | apply H0].
  eapply deduction_impp_trans with ((x1 -* y1) * x1).
  + rewrite <- provable_derivable.
    apply sepcon_mono; [apply provable_impp_refl | apply H].
  + rewrite <- provable_derivable.
    apply wand_sepcon_adjoint.
    apply provable_impp_refl.
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

Lemma deduction_sepcon_orp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x * (y || z) <-> Phi |-- x * y || x * z.
Proof.
  intros.
  split; intros; eapply deduction_modus_ponens; eauto.
  + eapply deduction_andp_elim1.
    apply derivable_sepcon_orp_right.
  + eapply deduction_andp_elim2.
    apply derivable_sepcon_orp_right.
Qed.

Lemma derivable_emp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {usL: UnitarySeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {usGamma: UnitarySeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x y: expr),
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

Lemma GC_Classical_collapse_aux: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {usL: UnitarySeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {usGamma: UnitarySeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (Phi: context) (x: expr),
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

Theorem GC_Classical_collapse: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {usL: UnitarySeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {usGamma: UnitarySeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr),
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

Module SeparationLogic.
Section SeparationLogic.

Context (Var: Type).

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance SL: SeparationLanguage L := UnitarySeparationLanguage.sL Var.
Instance uSL: UnitarySeparationLanguage L := UnitarySeparationLanguage.usL Var.

Require Import Logic.SeparationLogic.SoundCompleteParameter.

Context (PAR: SL_Parameter).

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: IC PAR = true -> forall x y, provable ((x --> y) || (y --> x))
| excluded_middle: EM PAR = true -> forall x, provable (x || ~~ x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_mono: forall x1 x2 y1 y2, provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2))
| sepcon_emp: EMP PAR = true -> forall x, provable (x * emp <--> x)
| sepcon_elim1: SCE PAR = true -> forall x y, provable (x * y --> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance sG: SeparationLogic L G.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
  + apply sepcon_mono.
Qed.

End SeparationLogic.
End SeparationLogic.

Module ReynoldsLogic.
Section ReynoldsLogic.

Context (Var: Type).

Instance L: Language := SeparationLanguage.L Var.
Instance nL: NormalLanguage L := SeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := SeparationLanguage.pL Var.
Instance SL: SeparationLanguage L := SeparationLanguage.sL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_mono: forall x1 x2 y1 y2, provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2))
| sepcon_elim1: forall x y, provable (x * y --> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance sG: SeparationLogic L G.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
  + apply sepcon_mono.
Qed.

Instance gcsG: GarbageCollectSeparationLogic L G.
Proof.
  constructor.
  apply sepcon_elim1.
Qed.

End ReynoldsLogic.
End ReynoldsLogic.

Module OHearnLogic.
Section OHearnLogic.

Context (Var: Type).

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance SL: SeparationLanguage L := UnitarySeparationLanguage.sL Var.
Instance usL: UnitarySeparationLanguage L := UnitarySeparationLanguage.usL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| excluded_middle: forall x, provable (x || ~~ x)
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_mono: forall x1 x2 y1 y2, provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2))
| sepcon_emp: forall x, provable (x * emp <--> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance cpG: ClassicalPropositionalLogic L G.
Proof.
  constructor.
  apply excluded_middle.
Qed.

Instance sG: SeparationLogic L G.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
  + apply sepcon_mono.
Qed.

Instance usG: UnitarySeparationLogic L G.
Proof.
  constructor.
  apply sepcon_emp.
Qed.

End OHearnLogic.
End OHearnLogic.

Module LogicOnModuResModel.
Section LogicOnModuResModel.

Context (Var: Type).

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance SL: SeparationLanguage L := UnitarySeparationLanguage.sL Var.
Instance usL: UnitarySeparationLanguage L := UnitarySeparationLanguage.usL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x))
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_mono: forall x1 x2 y1 y2, provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2))
| sepcon_emp: forall x, provable (x * emp <--> x)
| sepcon_elim1: forall x y, provable (x * y --> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance gdpG: GodelDummettPropositionalLogic L G.
Proof.
  constructor.
  apply impp_choice.
Qed.

Instance sG: SeparationLogic L G.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
  + apply sepcon_mono.
Qed.

Instance usG: UnitarySeparationLogic L G.
Proof.
  constructor.
  apply sepcon_emp.
Qed.

Instance gcsG: GarbageCollectSeparationLogic L G.
Proof.
  constructor.
  apply sepcon_elim1.
Qed.

End LogicOnModuResModel. 
End LogicOnModuResModel.

Module LogicOnMSL.
Section LogicOnMSL.

Context (Var: Type).

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance SL: SeparationLanguage L := UnitarySeparationLanguage.sL Var.
Instance usL: UnitarySeparationLanguage L := UnitarySeparationLanguage.usL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x))
| sepcon_comm: forall x y, provable (x * y --> y * x)
| sepcon_assoc: forall x y z, provable (x * (y * z) <--> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_mono: forall x1 x2 y1 y2, provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2))
| sepcon_emp: forall x, provable (x * emp <--> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance gdpG: GodelDummettPropositionalLogic L G.
Proof.
  constructor.
  apply impp_choice.
Qed.

Instance sG: SeparationLogic L G.
Proof.
  constructor.
  + apply sepcon_comm.
  + apply sepcon_assoc.
  + intros; split.
    - apply wand_sepcon_adjoint1.
    - apply wand_sepcon_adjoint2.
  + apply sepcon_mono.
Qed.

Instance usG: UnitarySeparationLogic L G.
Proof.
  constructor.
  apply sepcon_emp.
Qed.

End LogicOnMSL.
End LogicOnMSL.

