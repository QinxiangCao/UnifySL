Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.

Local Open Scope logic_base.
Local Open Scope syntax.

Definition multi_imp {L: Language} {nL: NormalLanguage L} (xs: list expr) (y: expr): expr :=
  fold_right impp y xs.

Class NormalProofTheory (L: Language) {nL: NormalLanguage L} (Gamma: ProofTheory L): Type := {
  derivable_provable: forall Phi y, derivable Phi y <->
                        exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y)
}.

Lemma provable_derivable {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall x, provable x <-> derivable empty_context x.
Proof.
  intros.
  rewrite derivable_provable.
  split; intros.
  + exists nil; split; auto.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    inversion H; subst.
    inversion H3.
Qed.

Lemma deduction_weaken {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi Psi x,
  Included _ Phi Psi ->
  Phi |-- x ->
  Psi |-- x.
Proof.
  intros.
  rewrite derivable_provable in H0 |- *.
  destruct H0 as [xs [? ?]].
  exists xs; split; auto.
  revert H0; apply Forall_impl.
  auto.
Qed.

Lemma deduction_weaken1 {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi x y,
  Phi |-- y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  eapply deduction_weaken; eauto.
  intros ? ?; left; auto.
Qed.

Lemma deduction_weaken0 {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi y,
  |-- y ->
  Phi |-- y.
Proof.
  intros.
  rewrite provable_derivable in H.
  eapply deduction_weaken; eauto.
  intros ? [].
Qed.

Lemma deduction_impp_elim {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi x y,
  Phi |-- impp x y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  rewrite derivable_provable in H |- *.
  destruct H as [xs [? ?]].
  exists (xs ++ (x :: nil)).
  split.
  + rewrite Forall_app_iff; split.
    - revert H; apply Forall_impl.
      intros.
      left; auto.
    - constructor; auto.
      right. constructor.
  + replace (multi_imp (xs ++ x :: nil) y) with (multi_imp xs (impp x y)); auto.
    clear.
    induction xs; auto.
    simpl; f_equal; auto.
Qed.

Definition Build_AxiomaticProofTheory {L: Language} {nL: NormalLanguage L} (Provable: expr -> Prop): ProofTheory L :=
  Build_ProofTheory L Provable
   (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ Provable (multi_imp xs y)).

Definition Build_nAxiomaticProofTheory {L: Language} {nL: NormalLanguage L} (Provable: expr -> Prop): NormalProofTheory L (Build_AxiomaticProofTheory Provable) :=
  Build_NormalProofTheory L nL (Build_AxiomaticProofTheory Provable) (fun _ _ => iff_refl _).

Definition Build_SequentCalculus {L: Language} {nL: NormalLanguage L} (Derivable: context -> expr -> Prop): ProofTheory L :=
  Build_ProofTheory L (fun x => Derivable (Empty_set _) x) Derivable.

Class MinimunPropositionalLogic (L: Language) {nL: NormalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} := {
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
}.

Lemma provable_impp_refl: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma aux_minimun_rule00: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma aux_minimun_theorem00: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  (y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  pose proof axiom2 x y z.
  pose proof aux_minimun_rule00 _ (y --> z) H.
  pose proof axiom1 (y --> z) x.
  pose proof axiom2 (y --> z) (x --> y --> z) ((x --> y) --> (x --> z)).
  pose proof modus_ponens _ _ H2 H0.
  pose proof modus_ponens _ _ H3 H1.
  auto.
Qed.

Lemma aux_minimun_rule01: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- (z --> x) --> (z --> y).
Proof.
  intros.
  pose proof aux_minimun_theorem00 z x y.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma aux_minimun_rule02: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof aux_minimun_theorem00 x y z.
  pose proof modus_ponens _ _ H1 H0.
  pose proof modus_ponens _ _ H2 H.
  auto.
Qed.

Lemma aux_minimun_theorem01: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  (x --> z) --> (x --> y --> z).
Proof.
  intros.
  apply aux_minimun_rule01.
  apply axiom1.
Qed.

Lemma aux_minimun_theorem02: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- x --> (x --> y) --> y.
Proof.
  intros.
  pose proof axiom2 (x --> y) x y.
  pose proof provable_impp_refl (x --> y).
  pose proof modus_ponens _ _ H H0.
  pose proof aux_minimun_rule01 _ _ x H1.
  pose proof axiom1 x (x --> y).
  pose proof modus_ponens _ _ H2 H3.
  auto.
Qed.

Lemma aux_minimun_theorem03: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |--  y --> (x --> y --> z) --> (x --> z).
Proof.
  intros.
  pose proof aux_minimun_theorem00 x (y --> z) z.
  pose proof aux_minimun_theorem02 y z.
  eapply aux_minimun_rule02; eauto.
Qed.

Lemma aux_minimun_theorem04: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y: expr), |-- (x --> x --> y) --> x --> y.
Proof.
  intros.
  pose proof axiom2 x (x --> y) y.
  pose proof aux_minimun_theorem02 x y.
  pose proof modus_ponens _ _ H H0.
  auto.
Qed.

Lemma provable_impp_arg_switch: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  apply aux_minimun_rule02 with (y --> x --> y --> z).
  + apply axiom1.
  + pose proof axiom2 y (x --> y --> z) (x --> z).
    eapply modus_ponens; eauto. clear H.
    pose proof aux_minimun_theorem00 x (y --> z) z.
    eapply aux_minimun_rule02; eauto.
    apply aux_minimun_theorem02.
Qed.

Lemma provable_impp_trans: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof provable_impp_arg_switch (y --> z) (x --> y) (x --> z).
  eapply modus_ponens; eauto. clear H.
  apply aux_minimun_theorem00.
Qed.

Lemma provable_multi_imp_shrink: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply aux_minimun_theorem04.
  + simpl.
    apply aux_minimun_rule01 with (z := a) in IHxs.
    eapply aux_minimun_rule02; [| eauto].
    apply provable_impp_arg_switch.
Qed.

Lemma provable_multi_imp_arg_switch1: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- (x --> multi_imp xs  y) --> multi_imp xs (x --> y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
    - apply provable_impp_arg_switch.
    - apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_arg_switch2: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- multi_imp xs (x --> y) --> (x --> multi_imp xs  y).
Proof.
  intros.
  induction xs.
  + simpl.
    apply provable_impp_refl.
  + simpl.
    apply aux_minimun_rule02 with (a --> x --> multi_imp xs y).
    - apply aux_minimun_rule01; auto.
    - apply provable_impp_arg_switch.
Qed.

Lemma provable_multi_imp_weaken: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (xs: list expr) (x y: expr), |-- x --> y -> |-- multi_imp xs x --> multi_imp xs y.
Proof.
  intros.
  induction xs.
  + auto.
  + apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_remove_rel: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (xs1 xs2: list expr) (x y: expr), remove_rel x xs1 xs2 -> |-- multi_imp xs1 y --> multi_imp xs2 (x --> y).
Proof.
  intros.
  induction H.
  + simpl.
    apply axiom1.
  + simpl.
    apply aux_minimun_rule02 with (a --> multi_imp ys (a --> y)).
    - apply aux_minimun_rule01; auto.
    - apply provable_multi_imp_shrink.
  + simpl.
    apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_split
      {L: Language}
      {nL: NormalLanguage L}
      {Gamma: ProofTheory L}
      {nGamma: NormalProofTheory L Gamma}
      {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall Phi1 Phi2 (xs: list expr) (y: expr),
    Forall (Union _ Phi1 Phi2) xs ->
    |-- multi_imp xs y ->
    exists xs1 xs2,
      Forall Phi1 xs1 /\
      Forall Phi2 xs2 /\
      |-- multi_imp xs1 (multi_imp xs2 y).
Proof.
  intros.
  revert y H0; induction H.
  + exists nil, nil.
    split; [| split]; [constructor .. | auto].
  + intros.
    specialize (IHForall (x --> y)).
    eapply modus_ponens in H1;
      [| simpl; apply provable_multi_imp_arg_switch1].
    specialize (IHForall H1); clear H1.
    destruct IHForall as [xs1 [xs2 [? [? ?]]]].
    destruct H.
    - exists (x :: xs1), xs2.
      split; [constructor | split]; auto.
      simpl; eapply modus_ponens; [apply provable_multi_imp_arg_switch2 |].
      eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
      apply provable_multi_imp_arg_switch2.
    - exists xs1, (x :: xs2).
      split; [| split; [constructor | ]]; auto.
      eapply modus_ponens; [apply provable_multi_imp_weaken | exact H3].
      simpl; apply provable_multi_imp_arg_switch2.
Qed.

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

Lemma derivable_assum: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi x -> Phi |-- x.
Proof.
  intros.
  rewrite derivable_provable.
  exists (x :: nil); split.
  + constructor; auto.
  + simpl.
    apply provable_impp_refl.
Qed.

Lemma derivable_assum1: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Union _ Phi (Singleton _ x) |-- x.
Proof.
  intros.
  apply derivable_assum.
  right; constructor.
Qed.

Lemma deduction_impp_intros: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
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
  + pose proof provable_multi_imp_remove_rel xs xs' x y H1.
    eapply modus_ponens; eauto.
Qed.

Theorem deduction_theorem {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply deduction_impp_intros; auto.
  + apply deduction_impp_elim; auto.
Qed.

Lemma provable_add_multi_imp_left_head: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1.
  + apply provable_impp_refl.
  + eapply aux_minimun_rule02; eauto.
    apply axiom1.
Qed.

Lemma provable_add_multi_imp_left_tail: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1; simpl.
  + pose proof (provable_add_multi_imp_left_head xs2 nil y).
    rewrite app_nil_r in H; auto.
  + apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
Proof.
  intros.
  induction xs; simpl.
  + apply aux_minimun_theorem02.
  + eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
    eapply aux_minimun_rule02; [| apply aux_minimun_theorem04].
    apply aux_minimun_rule01.
    eapply aux_minimun_rule02; [eauto |].
    eapply aux_minimun_rule02; [| apply provable_impp_arg_switch].
    apply aux_minimun_theorem00.
Qed.

Lemma deduction_modus_ponens: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- x --> y ->
  Phi |-- y.
Proof.
  intros.
  rewrite derivable_provable in H, H0 |- *.
  destruct H as [xs1 [? ?]], H0 as [xs2 [? ?]].
  exists (xs1 ++ xs2); split.
  + rewrite Forall_app_iff; auto.
  + pose proof modus_ponens _ _ (provable_add_multi_imp_left_tail xs1 xs2 _) H1.
    pose proof modus_ponens _ _ (provable_add_multi_imp_left_head xs1 xs2 _) H2.
    pose proof provable_multi_imp_modus_ponens (xs1 ++ xs2) x y.
    pose proof modus_ponens _ _ H5 H3.
    pose proof modus_ponens _ _ H6 H4.
    auto.
Qed.

Lemma derivable_impp_refl: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
  intros.
  apply deduction_theorem.
  apply derivable_assum1.
Qed.

Lemma deduction_left_impp_intros: forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y --> x.
Proof.
  intros.
  apply deduction_theorem.
  apply deduction_weaken1; auto.
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

(*

Theorem weak_completeness_reduce {L: Language} {nL: NormalLanguage L} (R: SyntacticReduction L) {nR: NormalSyntacticReduction L R} (Gamma: ProofTheory L) (SM: Semantics L) {rcGamma: ReductionConsistentProofTheory R Gamma} {rcSM: ReductionConsistentSemantics R SM}:
  (forall x, normal_form x -> |== x -> |-- x) ->
  weakly_complete Gamma SM.
Proof.
  intros; hnf; intros.
  destruct (reduce_to_norm x) as [y [? ?]].
  specialize (H y H2).
  rewrite (provable_reduce x y H1).
  apply H.
  intro m; specialize (H0 m).
  rewrite (sat_reduce x y m H1) in H0.
  auto.
Qed.


*)
