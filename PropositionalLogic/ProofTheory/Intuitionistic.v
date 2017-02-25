Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class IntuitionisticPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} := {
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y;
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z);
  falsep_elim: forall x, |-- FF --> x
}.

Lemma derivable_andp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> y --> x && y.
Proof.
  intros.
  pose proof andp_intros x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_andp_elim1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y --> x.
Proof.
  intros.
  pose proof andp_elim1 x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_andp_elim2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y --> y.
Proof.
  intros.
  pose proof andp_elim2 x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_orp_intros1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> x || y.
Proof.
  intros.
  pose proof orp_intros1 x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_orp_intros2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- y --> x || y.
Proof.
  intros.
  pose proof orp_intros2 x y.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_orp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  pose proof orp_elim x y z.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_falsep_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- FF --> x.
Proof.
  intros.
  pose proof falsep_elim x.
  apply deduction_weaken0; auto.
Qed.

Lemma deduction_andp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y ->
  Phi |-- x && y.
Proof.
  intros.
  pose proof derivable_andp_intros Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma deduction_andp_elim1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y ->
  Phi |-- x.
Proof.
  intros.
  pose proof derivable_andp_elim1 Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_andp_elim2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y ->
  Phi |-- y.
Proof.
  intros.
  pose proof derivable_andp_elim2 Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_orp_intros1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- x || y.
Proof.
  intros.
  pose proof derivable_orp_intros1 Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_orp_intros2: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- y ->
  Phi |-- x || y.
Proof.
  intros.
  pose proof derivable_orp_intros2 Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_orp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- x --> z ->
  Phi |-- y --> z ->
  Phi |-- x || y --> z.
Proof.
  intros.
  pose proof derivable_orp_elim Phi x y z.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma deduction_falsep_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- FF ->
  Phi |-- x.
Proof.
  intros.
  pose proof derivable_falsep_elim Phi x.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma derivable_double_negp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  unfold negp.
  apply derivable_modus_ponens.
Qed.

Lemma double_negp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x --> ~~ ~~ x.
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_double_negp_intros.
Qed.

Lemma deduction_double_negp_intros: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x ->
  Phi |-- ~~ ~~ x.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_double_negp_intros.
Qed.

Lemma derivable_contradiction_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> ~~ x --> y.
Proof.
  intros.
  pose proof derivable_double_negp_intros Phi x.
  pose proof derivable_falsep_elim Phi y.

  unfold negp at 1 in H.
  rewrite <- !deduction_theorem in H |- *.
  apply (deduction_weaken1 _ x) in H0.
  apply (deduction_weaken1 _ (~~ x)) in H0.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_contradiction_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- ~~ x ->
  Phi |-- y.
Proof.
  intros.
  pose proof derivable_contradiction_elim Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma derivable_iffp_refl: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <--> x.
Proof.
  intros.
  apply deduction_andp_intros; apply derivable_impp_refl.
Qed.

Lemma provable_iffp_refl: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply derivable_iffp_refl.
Qed.

Lemma contrapositivePP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- (y --> x) --> ~~ x --> ~~ y.
Proof.
  intros.
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  apply aux_minimun_theorem00.
Qed.

Lemma deduction_contrapositivePP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePP.
Qed.

Lemma contrapositivePN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- (y --> ~~ x) --> (x --> ~~ y).
Proof.
  intros.
  apply provable_impp_arg_switch.
Qed.

Lemma deduction_contrapositivePN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePN.
Qed.

Lemma demorgan_orp_negp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- ~~ x || ~~ y --> ~~ (x && y).
Proof.
  intros.
  rewrite provable_derivable.
  unfold negp at 3.
  rewrite <- !deduction_theorem.
  apply (deduction_modus_ponens _ (~~ x || ~~ y)).
  + apply deduction_weaken1.
    apply derivable_assum1.
  + apply deduction_orp_elim.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ x); [| apply derivable_assum1].
      apply deduction_weaken1.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ y); [| apply derivable_assum1].
      apply deduction_weaken1.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma demorgan_negp_orp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- ~~ (x || y) <--> (~~ x && ~~ y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros. 
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros1.
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros2.
  + rewrite <- deduction_theorem.
    apply deduction_orp_elim.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma andp_comm: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- x && y <--> y && x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
Qed.

Lemma andp_assoc: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y z: expr),
  |-- x && y && z <--> x && (y && z).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; [| apply deduction_andp_intros].
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; [apply deduction_andp_intros |].
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma orp_comm: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y: expr),
  |-- x || y <--> y || x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim; rewrite <- provable_derivable.
    - apply orp_intros2.
    - apply orp_intros1.
  + apply deduction_orp_elim; rewrite <- provable_derivable.
    - apply orp_intros2.
    - apply orp_intros1.
Qed.

Lemma orp_assoc: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x y z: expr),
  |-- x || y || z <--> x || (y || z).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim; [apply deduction_orp_elim |]; rewrite <- deduction_theorem.
    - apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros2.
      apply derivable_assum1.
  + apply deduction_orp_elim; [| apply deduction_orp_elim]; rewrite <- deduction_theorem.
    - apply deduction_orp_intros1.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros1.
      apply deduction_orp_intros2.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply derivable_assum1.
Qed.

Lemma andp_truep: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x && TT <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_assum1.
    - apply derivable_impp_refl.
Qed.

Lemma truep_andp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- TT && x <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim2.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_impp_refl.
    - apply derivable_assum1.
Qed.

Lemma falsep_orp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- FF || x <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim.
    - apply derivable_falsep_elim.
    - apply derivable_impp_refl.
  + apply derivable_orp_intros2.
Qed.

Lemma orp_falsep: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x || FF <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim.
    - apply derivable_impp_refl.
    - apply derivable_falsep_elim.
  + apply derivable_orp_intros1.
Qed.

Lemma andp_dup: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x && x <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; apply derivable_assum1.
Qed.

Lemma orp_dup: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (x: expr),
  |-- x || x <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim; apply derivable_impp_refl.
  + apply derivable_orp_intros1.
Qed.

