Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class MinimunPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) := {
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
}.

Lemma imp_refl: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma add_imp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma aux_minimun_theorem00: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  (y --> z) --> (x --> y) --> (x --> z).
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

Lemma remove_iden_assum_from_imp: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- (z --> x) --> (z --> y).
Proof.
  intros.
  pose proof aux_minimun_theorem00 z x y.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma imp_trans: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof aux_minimun_theorem00 x y z.
  pose proof modus_ponens _ _ H1 H0.
  pose proof modus_ponens _ _ H2 H.
  auto.
Qed.

Lemma aux_minimun_theorem01: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  (x --> z) --> (x --> y --> z).
Proof.
  intros.
  apply remove_iden_assum_from_imp.
  apply axiom1.
Qed.

Lemma aux_minimun_theorem02: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- x --> (x --> y) --> y.
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

Lemma aux_minimun_theorem03: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  y --> (x --> y --> z) --> (x --> z).
Proof.
  intros.
  pose proof aux_minimun_theorem00 x (y --> z) z.
  pose proof aux_minimun_theorem02 y z.
  eapply imp_trans; eauto.
Qed.

Lemma aux_minimun_theorem04: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- (x --> x --> y) --> x --> y.
Proof.
  intros.
  pose proof axiom2 x (x --> y) y.
  pose proof aux_minimun_theorem02 x y.
  pose proof modus_ponens _ _ H H0.
  auto.
Qed.

Lemma imp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  apply imp_trans with (y --> x --> y --> z).
  + apply axiom1.
  + pose proof axiom2 y (x --> y --> z) (x --> z).
    eapply modus_ponens; eauto. clear H.
    pose proof aux_minimun_theorem00 x (y --> z) z.
    eapply imp_trans; eauto.
    apply aux_minimun_theorem02.
Qed.

Lemma imp_trans_strong: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof imp_arg_switch (y --> z) (x --> y) (x --> z).
  eapply modus_ponens; eauto. clear H.
  apply aux_minimun_theorem00.
Qed.

Lemma multi_imp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply aux_minimun_theorem04.
  + simpl.
    apply remove_iden_assum_from_imp with (z := a) in IHxs.
    eapply imp_trans; [| eauto].
    apply imp_arg_switch.
Qed.

Lemma multi_imp_remove_rel: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} (xs1 xs2: list expr) (x y: expr), remove_rel x xs1 xs2 -> |-- multi_imp xs1 y --> multi_imp xs2 (x --> y).
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

Lemma derivable_assum: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi x -> Phi |-- x.
Proof.
  intros.
  rewrite derivable_provable.
  exists (x :: nil); split.
  + constructor; auto.
  + simpl.
    apply imp_refl.
Qed.

Lemma derivable_assum1: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Union _ Phi (Singleton _ x) |-- x.
Proof.
  intros.
  apply derivable_assum.
  right; constructor.
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

Lemma impp_elim: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
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

Theorem deduction_theorem {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply impp_elim; auto.
  + apply impp_intros; auto.
Qed.

Lemma add_multi_imp_left_head: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1.
  + apply imp_refl.
  + eapply imp_trans; eauto.
    apply axiom1.
Qed.

Lemma add_multi_imp_left_tail: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1; simpl.
  + pose proof (add_multi_imp_left_head xs2 nil y).
    rewrite app_nil_r in H; auto.
  + apply remove_iden_assum_from_imp; auto.
Qed.

Lemma multi_imp_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {mpGamma: MinimunPropositionalLogic L Gamma} xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
Proof.
  intros.
  induction xs; simpl.
  + apply aux_minimun_theorem02.
  + eapply imp_trans; [| apply imp_arg_switch].
    eapply imp_trans; [| apply aux_minimun_theorem04].
    apply remove_iden_assum_from_imp.
    eapply imp_trans; [eauto |].
    eapply imp_trans; [| apply imp_arg_switch].
    apply aux_minimun_theorem00.
Qed.

Lemma derivable_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
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

Lemma derivable_imp_refl: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
  intros.
  apply deduction_theorem.
  apply derivable_assum1.
Qed.

Lemma derivable_add_imp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y --> x.
Proof.
  intros.
  apply deduction_theorem.
  apply derivable_weaken1; auto.
Qed.

Lemma axiom1_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x --> y --> x.
Proof.
  intros.
  rewrite derivable_provable.
  exists nil.
  split; [constructor | apply axiom1].
Qed.

Lemma axiom2_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite derivable_provable.
  exists nil.
  split; [constructor | apply axiom2].
Qed.

Lemma derivable_closed_element_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; intros; auto.
  apply derivable_assum; auto.
Qed.

Lemma maximal_consistent_derivable_closed: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  derivable_closed Phi.
Proof.
  intros.
  hnf; intros.
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

Lemma MCS_element_derivable: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context),
  maximal_consistent Gamma Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  apply derivable_closed_element_derivable, maximal_consistent_derivable_closed.
  auto.
Qed.
