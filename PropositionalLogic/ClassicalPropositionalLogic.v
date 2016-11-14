Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class ClassicalPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  excluded_middle: forall x, |-- x || ~~ x
}.

Lemma derivable_excluded_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x || ~~ x.
Proof.
  intros.
  pose proof excluded_middle x.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_double_negp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ (~~ x) --> x.
Proof.
  intros.
  unfold negp.
  pose proof derivable_orp_elim Phi x (x --> FF) (((x --> FF) --> FF) --> x).
  pose proof derivable_axiom1 Phi x ((x --> FF) --> FF).
  pose proof deduction_modus_ponens _ _ _ H0 H.
  clear H H0.

  pose proof derivable_contradiction_elim Phi (x --> FF) x.
  pose proof deduction_modus_ponens _ _ _ H H1.
  clear H H1.

  pose proof derivable_excluded_middle Phi x.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_double_negp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <-> Phi |-- ~~ ~~ x.
Proof.
  intros.
  split; intros; eapply deduction_modus_ponens; eauto.
  + apply derivable_double_negp_intros.
  + apply derivable_double_negp_elim.
Qed.

(*
Lemma contrapositivePP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  intros.
  apply deduction_theorem.
  apply (derivable_weaken1 _ x) in H.
  pose proof derivable_assum1 Phi x.
  apply (derivable_add_imp_left _ _ (~~ y)) in H0.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr x)) y x.
  pose proof derivable_modus_ponens _ _ _ H0 H1.
  pose proof derivable_modus_ponens _ _ _ H H2.
  auto.
Qed.

Lemma contrapositiveNN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  apply derivable_weaken1; eauto.
Qed.

Lemma contrapositiveNP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply deduction_theorem; auto.
Qed.

Lemma contrapositivePN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  apply derivable_weaken1; auto.
Qed.

Lemma assum_exclude_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- ~~ x --> y ->
  Phi |-- x --> y ->
  Phi |-- y.
Proof.
  intros.
  apply contrapositiveNN in H0.
  apply contrapositiveNP in H.
  pose proof axiom3_derivable Phi y x.
  pose proof derivable_modus_ponens _ _ _ H H1.
  pose proof derivable_modus_ponens _ _ _ H0 H2.
  auto.
Qed.


*)

Lemma classical_derivable_spec: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <-> ~ consistent (Union _ Phi (Singleton _ (~~ x))).
Proof.
  intros.
  rewrite deduction_double_negp.
  unfold negp at 1.
  rewrite <- deduction_theorem.
  rewrite consistent_spec.
  tauto.
Qed.

Lemma MCS_nonelement_inconsistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x: expr, ~ Phi x <-> Phi |-- x --> FF).
Proof.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 (Union _ Phi (Singleton _ x))).
    rewrite consistent_spec in H1.
    rewrite deduction_theorem in H1.
    assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
    assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
    tauto.
  + intro.
    pose proof derivable_assum Phi x H1.
    pose proof deduction_modus_ponens _ _ _ H2 H0.
    destruct H as [? _].
    rewrite consistent_spec in H; auto.
Qed.

Lemma MCS_andp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  apply maximal_consistent_derivable_closed in H.
  apply DCS_andp_iff; auto.
Qed.

Lemma MCS_orp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  split; intros.
  + destruct (Classical_Prop.classic (Phi x)); auto.
    destruct (Classical_Prop.classic (Phi y)); auto.
    exfalso.
    rewrite MCS_nonelement_inconsistent in H1 by auto.
    rewrite MCS_nonelement_inconsistent in H2 by auto.
    rewrite MCS_element_derivable in H0 by auto.
    pose proof deduction_orp_elim Phi x y FF H1 H2.
    pose proof deduction_modus_ponens _ _ _ H0 H3.
    destruct H as [? _].
    rewrite consistent_spec in H; auto.
  + destruct H0; rewrite MCS_element_derivable in H0 |- * by auto.
    - pose proof deduction_orp_intros1 Phi x y H0; auto.
    - pose proof deduction_orp_intros2 Phi x y H0; auto.
Qed.

Lemma MCS_impp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (deduction_modus_ponens _ x y); auto.
  + pose proof derivable_excluded_middle Phi y.
    rewrite <- MCS_element_derivable in H1 by auto.
    rewrite MCS_orp_iff in H1 by auto.
    pose proof derivable_excluded_middle Phi x.
    rewrite <- MCS_element_derivable in H2 by auto.
    rewrite MCS_orp_iff in H2 by auto.
    destruct H1; [| destruct H2].
    - rewrite MCS_element_derivable in H1 |- * by auto.
      apply deduction_left_impp_intros; auto.
    - exfalso.
      apply H0 in H2.
      rewrite MCS_element_derivable in H1, H2 by auto.
      pose proof deduction_modus_ponens _ _ _ H2 H1.
      destruct H as [? _].
      rewrite consistent_spec in H; auto.
    - rewrite MCS_element_derivable in H2 |- * by auto.
      unfold negp in H2.
      rewrite <- deduction_theorem in H2 |- *.
      pose proof deduction_falsep_elim _ y H2.
      auto.
Qed.

Lemma DCS_negp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  consistent Phi ->
  (forall x: expr, Phi x <-> ~ Phi (~~ x)).
Proof.
  intros.
  split; intros.
  + rewrite derivable_closed_element_derivable in H2 |- * by auto.
    intro.
    pose proof deduction_modus_ponens _ _ _ H2 H3.
    rewrite consistent_spec in H1; apply H1; auto.
  + rewrite derivable_closed_element_derivable in H2 |- * by auto.
    pose proof derivable_excluded_middle Phi x.
    specialize (H0 x (~~ x)).
    rewrite derivable_closed_element_derivable in H0 by auto.
    apply H0 in H3.
    destruct H3; rewrite derivable_closed_element_derivable in H3 by auto; auto.
    tauto.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

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
| excluded_middle: forall x, provable (x || (x --> FF)).

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

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

