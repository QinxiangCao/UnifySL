Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class ClassicalPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) := {
  syntactic_reduction_rule: forall x y, @reduce _ MendelsonReduction x y -> (|-- x <-> |-- y);
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z));
  axiom3: forall x y, |-- ((~~ y --> x) --> (~~ y --> ~~ x) --> y);
  true_provable: provable TT
}.

Lemma imp_refl: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma add_imp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma aux_classic_theorem00: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |--  (y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  pose proof axiom2 x y z.
  pose proof add_imp_left _ (y --> z) H.
  pose proof axiom1 (y --> z) x.
  pose proof axiom2 (y --> z) (x --> y --> z) ((x --> y) --> (x --> z)).
  pose proof modus_ponens _ _ H2 H0.
  pose proof modus_ponens _ _ H3 H1.
  auto.
Qed.

Lemma remove_iden_assum_from_imp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- (z --> x) --> (z --> y).
Proof.
  intros.
  pose proof aux_classic_theorem00 z x y.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma imp_trans: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof aux_classic_theorem00 x y z.
  pose proof modus_ponens _ _ H1 H0.
  pose proof modus_ponens _ _ H2 H.
  auto.
Qed.

Lemma aux_classic_theorem01: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |--  (x --> z) --> (x --> y --> z).
Proof.
  intros.
  apply remove_iden_assum_from_imp.
  apply axiom1.
Qed.

Lemma aux_classic_theorem02: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr), |-- x --> (x --> y) --> y.
Proof.
  intros.
  pose proof axiom2 (x --> y) x y.
  pose proof imp_refl (x --> y).
  pose proof modus_ponens _ _ H H0.
  pose proof remove_iden_assum_from_imp _ _ x H1.
  pose proof axiom1 x (x --> y).
  pose proof modus_ponens _ _ H2 H3.
  auto.
Qed.

Lemma aux_classic_theorem03: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |--  y --> (x --> y --> z) --> (x --> z).
Proof.
  intros.
  pose proof aux_classic_theorem00 x (y --> z) z.
  pose proof aux_classic_theorem02 y z.
  eapply imp_trans; eauto.
Qed.

Lemma aux_classic_theorem04: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr), |-- (x --> x --> y) --> x --> y.
Proof.
  intros.
  pose proof axiom2 x (x --> y) y.
  pose proof aux_classic_theorem02 x y.
  pose proof modus_ponens _ _ H H0.
  auto.
Qed.

Lemma imp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  apply imp_trans with (y --> x --> y --> z).
  + apply axiom1.
  + pose proof axiom2 y (x --> y --> z) (x --> z).
    eapply modus_ponens; eauto. clear H.
    pose proof aux_classic_theorem00 x (y --> z) z.
    eapply imp_trans; eauto.
    apply aux_classic_theorem02.
Qed.

Lemma imp_trans_strong: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof imp_arg_switch (y --> z) (x --> y) (x --> z).
  eapply modus_ponens; eauto. clear H.
  apply aux_classic_theorem00.
Qed.

Lemma multi_imp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply aux_classic_theorem04.
  + simpl.
    apply remove_iden_assum_from_imp with (z := a) in IHxs.
    eapply imp_trans; [| eauto].
    apply imp_arg_switch.
Qed.

Lemma multi_imp_remove_rel: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (xs1 xs2: list expr) (x y: expr), remove_rel x xs1 xs2 -> |-- multi_imp xs1 y --> multi_imp xs2 (x --> y).
Proof.
  intros.
  induction H.
  + simpl.
    apply axiom1.
  + simpl.
    apply imp_trans with (a --> multi_imp ys (a --> y)).
    - apply remove_iden_assum_from_imp; auto.
    - apply multi_imp_arg_switch.
  + simpl.
    apply remove_iden_assum_from_imp; auto.
Qed.

Lemma derive_assum: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi x -> Phi |-- x.
Proof.
  intros.
  rewrite derivable_provable.
  exists (x :: nil); split.
  + constructor; auto.
  + simpl.
    apply imp_refl.
Qed.

Lemma remove_rel_result_belong: forall (A : Type) (l1 l2 : list A) (x : A), remove_rel x l1 l2 -> Forall (fun y => In y l1) l2.
Proof.
  intros.
  induction H.
  + auto.
  + simpl.
    revert IHremove_rel; apply Forall_impl.
    intros; auto.
  + constructor; simpl; auto.
    revert IHremove_rel; apply Forall_impl.
    intros; auto.
Qed.

Lemma impp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Union _ Phi (Singleton _ x) |-- y ->
  Phi |-- x --> y.
Proof.
  intros.
  rewrite derivable_provable in H |- *.
  destruct H as [xs [? ?]].
  pose proof remove_rel_exist _ xs x (fun x => Classical_Prop.classic _).
  destruct H1 as [xs' ?].
  exists xs'; split.
  + pose proof remove_rel_result_belong _ _ _ _ H1.
    pose proof remove_rel_In _ _ _ _ H1.
    rewrite Forall_forall in H, H2 |- *.
    intros x0 HH; specialize (H2 x0 HH).
    specialize (H x0 H2).
    destruct H; auto.
    inversion H; subst; contradiction.
  + pose proof multi_imp_remove_rel xs xs' x y H1.
    eapply modus_ponens; eauto.
Qed.

Theorem deduction_theorem {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply impp_elim; auto.
  + apply impp_intros; auto.
Qed.

Lemma add_multi_imp_left_head: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1.
  + apply imp_refl.
  + eapply imp_trans; eauto.
    apply axiom1.
Qed.

Lemma add_multi_imp_left_tail: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1; simpl.
  + pose proof (add_multi_imp_left_head xs2 nil y).
    rewrite app_nil_r in H; auto.
  + apply remove_iden_assum_from_imp; auto.
Qed.

Lemma multi_imp_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
Proof.
  intros.
  induction xs; simpl.
  + apply aux_classic_theorem02.
  + eapply imp_trans; [| apply imp_arg_switch].
    eapply imp_trans; [| apply aux_classic_theorem04].
    apply remove_iden_assum_from_imp.
    eapply imp_trans; [eauto |].
    eapply imp_trans; [| apply imp_arg_switch].
    apply aux_classic_theorem00.
Qed.

Lemma derivable_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- x --> y ->
  Phi |-- y.
Proof.
  intros.
  rewrite derivable_provable in H, H0 |- *.
  destruct H as [xs1 [? ?]], H0 as [xs2 [? ?]].
  exists (xs1 ++ xs2); split.
  + rewrite Forall_app_iff; auto.
  + pose proof modus_ponens _ _ (add_multi_imp_left_tail xs1 xs2 _) H1.
    pose proof modus_ponens _ _ (add_multi_imp_left_head xs1 xs2 _) H2.
    pose proof multi_imp_modus_ponens (xs1 ++ xs2) x y.
    pose proof modus_ponens _ _ H5 H3.
    pose proof modus_ponens _ _ H6 H4.
    auto.
Qed.

Lemma axiom1_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> y --> x.
Proof.
  intros.
  rewrite derivable_provable.
  exists nil.
  split; [constructor | apply axiom1].
Qed.

Lemma axiom2_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite derivable_provable.
  exists nil.
  split; [constructor | apply axiom2].
Qed.

Lemma axiom3_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x.
Proof.
  intros.
  rewrite derivable_provable.
  exists nil.
  split; [constructor | apply axiom3].
Qed.

Lemma contradiction_rule: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- ~~ x ->
  Phi |-- x ->
  Phi |-- y.
Proof.
  intros.
  pose proof axiom3_derivable Phi y x.
  eapply derive_weaken with (Psi := Union _ Phi (Singleton _ (~~ y))) in H; [| intros ? ?; left; auto].
  apply deduction_theorem in H.
  eapply derive_weaken with (Psi := Union _ Phi (Singleton _ (~~ y))) in H0; [| intros ? ?; left; auto].
  apply deduction_theorem in H0.
  pose proof derivable_modus_ponens _ _ _ H0 H1.
  pose proof derivable_modus_ponens _ _ _ H H2.
  auto.
Qed.

Lemma double_negp_add: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ (~~ x) --> x.
Proof.
  intros.
  apply deduction_theorem.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr (~~ (~~ x)))) x (~~ x).
  pose proof imp_refl (~~ x).
  rewrite provable_derivable in H0.
  eapply derive_weaken with (Psi := Union _ Phi (Singleton _ (~~ (~~ x)))) in H0; [| intros ? []].
  pose proof derivable_modus_ponens _ _ _ H0 H.
  pose proof derive_assum (Union expr (Union expr Phi (Singleton expr (~~ ~~ x))) (Singleton _ (~~ x))) (~~ ~~ x).
  apply deduction_theorem in H2; [| left; right; constructor].
  pose proof derivable_modus_ponens _ _ _ H2 H1.
  auto.
Qed.

Lemma double_negp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  apply deduction_theorem.
  pose proof axiom3_derivable (Union expr Phi (Singleton expr x)) (~~ ~~ x) x.
  apply derivable_modus_ponens in H; [| apply deduction_theorem; apply axiom1_derivable].
  apply derivable_modus_ponens in H; [| apply double_negp_add].
  auto.
Qed.

Lemma contrapositivePP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  intros.
  apply deduction_theorem.
  eapply derive_weaken with (Psi := Union _ Phi (Singleton _ x)) in H; [| intros ? ?; left; auto].
  pose proof derive_assum (Union expr (Union expr Phi (Singleton expr x)) (Singleton _ (~~ y))) x.
  apply deduction_theorem in H0; [| left; right; constructor].
  pose proof axiom3_derivable (Union expr Phi (Singleton expr x)) y x.
  pose proof derivable_modus_ponens _ _ _ H0 H1.
  pose proof derivable_modus_ponens _ _ _ H H2.
  auto.
Qed.

Lemma contrapositiveNN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  eapply derive_weaken; eauto.
  intros ? ?; left; auto.
Qed.

Lemma contrapositiveNP: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  eapply derivable_modus_ponens; [| apply double_negp_elim].
  apply deduction_theorem; auto.
Qed.

Lemma contrapositivePN: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  intros.
  apply contrapositivePP.
  apply deduction_theorem.
  apply derivable_modus_ponens with y; [apply deduction_theorem, double_negp_add |].
  eapply derive_weaken; eauto.
  intros ? ?; left; auto.
Qed.

Lemma assum_exclude_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context) (x y: expr),
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

Lemma MCS_element_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; [apply derive_assum | intros].
  assert (consistent Gamma (Union _ Phi (Singleton _ x))).
  Focus 1. {
    intro.
    pose proof impp_elim _ _ _ H1.
    pose proof derivable_modus_ponens _ _ _ H0 H2.
    destruct H; auto.
  } Unfocus.
  destruct H.
  specialize (H2 _ H1).
  specialize (H2 (fun x H => Union_introl _ _ _ x H)).
  apply H2.
  right; constructor.
Qed.

Lemma MCS_nonelement_inconsistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  (forall x: expr, ~ Phi x <-> Phi |-- x --> FF).
Proof.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 (Union _ Phi (Singleton _ x))).
    unfold consistent in H1.
    rewrite deduction_theorem in H1.
    assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
    assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
    tauto.
  + intro.
    pose proof derive_assum Phi x H1.
    pose proof derivable_modus_ponens _ _ _ H2 H0.
    destruct H; auto.
Qed.

Lemma MCS_negp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  (forall x: expr, Phi (~~ x) <-> ~ Phi x).
Proof.
  intros.
  rewrite MCS_nonelement_inconsistent by auto.
  rewrite MCS_element_derivable by auto.
  split; intros.
  + apply deduction_theorem.
    apply (contradiction_rule _ x).
    - eapply derive_weaken; eauto.
      intros ? ?; left; auto.
    - apply derive_assum; right; constructor.
  + eapply derivable_modus_ponens with TT.
    - rewrite derivable_provable; exists nil.
      split; [auto |].
      apply true_provable.
    - apply contrapositivePN.
      eapply derivable_modus_ponens; eauto.
      rewrite derivable_provable; exists nil.
      split; [auto | simpl].
      eapply syntactic_reduction_rule.
      * apply imp_reduce; [| apply reduce_refl].
        apply imp_reduce; [apply reduce_refl |].
        apply reduce_step.
        eapply (propag_reduce_spec _ _ _ nil).
        right; right; constructor.
      * simpl.
        apply imp_refl.
Qed.

Lemma MCS_impp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (derivable_modus_ponens _ x y); auto.
  + assert (~ Phi x \/ Phi y) by tauto.
    clear H0; destruct H1.
    - rewrite <- MCS_negp_iff in H0 by auto.
      rewrite MCS_element_derivable in H0 |- * by auto.
      apply deduction_theorem.
      apply (contradiction_rule _ x).
      * eapply derive_weaken; eauto.
        intros ? ?; left; auto.
      * apply derive_assum; right; constructor.
    - rewrite MCS_element_derivable in H0 |- * by auto.
      pose proof axiom1_derivable Phi y x.
      apply (derivable_modus_ponens _ y); auto.
Qed.

Lemma classic_mendelson_consistent: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma}, reduction_consistent_prooftheory MendelsonReduction Gamma.
Proof.
  intros.
  apply reduction_consistent_prooftheory_from_provable; auto.
  hnf; intros.
  apply syntactic_reduction_rule; auto.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.

Context (Var: Type).

Inductive provable: @expr (PropositionalLanguage.L Var) -> Prop :=
| syntactic_reduction_rule1: forall x y, @reduce _ MendelsonReduction x y -> provable x -> provable y
| syntactic_reduction_rule2: forall x y, @reduce _ MendelsonReduction x y -> provable y -> provable x
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y)
| true_provable: provable TT.
(* Elliott Mendelson, Introduction to Mathematical Logic, Second Edition (New York: D. Van Nostrand, 1979) *)

Instance AG: AxiomaticProofTheory.AxiomaticProofTheory (PropositionalLanguage.L Var) :=
  AxiomaticProofTheory.Build_AxiomaticProofTheory (PropositionalLanguage.L Var) provable.

Instance G: ProofTheory (PropositionalLanguage.L Var) := AxiomaticProofTheory.G AG.

Instance cpG: ClassicalPropositionalLogic (PropositionalLanguage.L Var) G.
Proof.
  constructor.
  + split.
    - apply syntactic_reduction_rule1; auto. 
    - apply syntactic_reduction_rule2; auto. 
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
  + apply axiom3.
  + apply true_provable.
Qed.

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

