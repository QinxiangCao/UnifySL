Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class IntuitionisticPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {mpGamma: MinimunPropositionalLogic L Gamma} := {
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y;
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z);
  falsep_elim: forall x, |-- FF --> x
}.

Lemma andp_intros_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> y --> x && y.
Proof.
  intros.
  pose proof andp_intros x y.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma andp_elim1_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y --> x.
Proof.
  intros.
  pose proof andp_elim1 x y.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma andp_elim2_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x && y --> y.
Proof.
  intros.
  pose proof andp_elim2 x y.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma orp_intros1_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> x || y.
Proof.
  intros.
  pose proof orp_intros1 x y.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma orp_intros2_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- y --> x || y.
Proof.
  intros.
  pose proof orp_intros2 x y.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma orp_elim_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  pose proof orp_elim x y z.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma falsep_elim_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- FF --> x.
Proof.
  intros.
  pose proof falsep_elim x.
  rewrite provable_derivable in H.
  eapply derivable_weaken; eauto.
  intros ? [].
Qed.

Lemma DCS_andp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  rewrite !H0; clear H0; split; intros.
  + pose proof andp_elim1_derivable Phi x y.
    pose proof andp_elim2_derivable Phi x y.
    split; apply derivable_modus_ponens with (x && y); auto.
  + pose proof andp_intros_derivable Phi x y.
    destruct H.
    apply derivable_modus_ponens with y; auto.
    apply derivable_modus_ponens with x; auto.
Qed.

Lemma DCS_orp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  pose proof derivable_closed_element_derivable _ H; clear H.
  split; intros.
  + apply H0; auto.
  + rewrite !H1 in *.
    destruct H.
    - pose proof orp_intros1_derivable Phi x y.
      apply derivable_modus_ponens with x; auto.
    - pose proof orp_intros2_derivable Phi x y.
      apply derivable_modus_ponens with y; auto.
Qed.

Module IntuitionisticPropositionalLogic.
Section IntuitionisticPropositionalLogic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance R: SyntacticReduction L := IntuitionisticReduction.

Inductive provable: expr -> Prop :=
| syntactic_reduction_rule1: forall x y, reduce x y -> provable x -> provable y
| syntactic_reduction_rule2: forall x y, reduce x y -> provable y -> provable x
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance rcG: ReductionConsistentProofTheory IntuitionisticReduction G.
Proof.
  apply Build1_ReductionConsistentProofTheory.
  constructor.
  + apply syntactic_reduction_rule1; auto.
  + apply syntactic_reduction_rule2; auto.
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

End IntuitionisticPropositionalLogic.
End IntuitionisticPropositionalLogic.

