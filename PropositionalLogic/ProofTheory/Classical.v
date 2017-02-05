Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

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

Lemma double_negp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_double_negp_elim.
  + apply derivable_double_negp_intros.
Qed.

Lemma deduction_double_negp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x <-> Phi |-- ~~ ~~ x.
Proof.
  intros.
  split; intros; eapply deduction_modus_ponens; eauto.
  + apply derivable_double_negp_intros.
  + apply derivable_double_negp_elim.
Qed.

Instance Classical2GodelDummett {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}: GodelDummettPropositionalLogic L Gamma.
Proof.
  constructor.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.
  pose proof derivable_excluded_middle Phi x.
  eapply deduction_modus_ponens; [exact H |].
  apply deduction_orp_elim.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    rewrite deduction_theorem.
    apply derivable_axiom1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros1.
    rewrite deduction_theorem.
    apply deduction_impp_arg_switch.
    apply derivable_contradiction_elim.
Qed.

Lemma contrapositiveNN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr),
  |-- (~~ y --> ~~ x) --> (x --> y).
Proof.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  rewrite <- deduction_theorem.
  rewrite deduction_double_negp.
  rewrite -> deduction_theorem.
  apply deduction_contrapositivePN.
  apply derivable_assum1.
Qed.

Lemma contrapositiveNP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr),
  |-- (~~ y --> x) --> (~~ x --> y).
Proof.
  intros.
  rewrite <- (contrapositiveNN (~~ x) y).
  rewrite provable_derivable.
  do 2 rewrite <- deduction_theorem.
  rewrite <- deduction_double_negp.
  do 2 rewrite -> deduction_theorem.
  rewrite <- provable_derivable.
  apply provable_impp_refl.
Qed.

Lemma deduction_contrapositiveNN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  intros.
  rewrite <- contrapositiveNN.
  auto.
Qed.

Lemma deduction_contrapositiveNP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}  {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  intros.
  rewrite <- contrapositiveNP.
  auto.
Qed.

Lemma impp2orp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}  {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr),
  |-- (x --> y) <--> (~~ x || y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x || ~~ x)); [apply derivable_excluded_middle |].
    apply deduction_orp_elim.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros1.
      apply derivable_assum1.
  + apply deduction_orp_elim.
    - rewrite <- deduction_theorem.
      rewrite <- deduction_theorem.
      apply deduction_falsep_elim.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - apply derivable_axiom1.
Qed.

(*
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
