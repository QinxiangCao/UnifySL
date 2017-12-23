Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.ProofTheory.TheoryOfSequentCalculus.

Local Open Scope logic_base.
Local Open Scope syntax.

(* TODO: Change this file name to minimun. *)

Definition multi_imp {L: Language} {minL: MinimunLanguage L} (xs: list expr) (y: expr): expr :=
  fold_right impp y xs.

Class NormalAxiomatization (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L): Type := {
  derivable_provable: forall Phi y, derivable Phi y <->
                        exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y)
}.

Class MinimunAxiomatization (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) := {
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
}.

Class MinimunSequentCalculus (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) := {
  deduction_modus_ponens: forall Phi x y, Phi |-- x -> Phi |-- x --> y -> Phi |-- y;
  deduction_impp_intros: forall Phi x y, Phi;; x |-- y -> Phi |-- x --> y
}.

Section DerivableRulesFromAxiomatization.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_impp_refl: forall (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma aux_minimun_rule00: forall (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma aux_minimun_theorem00: forall (x y z: expr), |--  (y --> z) --> (x --> y) --> (x --> z).
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

Lemma aux_minimun_rule01: forall (x y z: expr), |-- x --> y -> |-- (z --> x) --> (z --> y).
Proof.
  intros.
  pose proof aux_minimun_theorem00 z x y.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma aux_minimun_rule02: forall (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof aux_minimun_theorem00 x y z.
  pose proof modus_ponens _ _ H1 H0.
  pose proof modus_ponens _ _ H2 H.
  auto.
Qed.

Lemma aux_minimun_theorem01: forall (x y z: expr), |-- (x --> z) --> (x --> y --> z).
Proof.
  intros.
  apply aux_minimun_rule01.
  apply axiom1.
Qed.

Lemma aux_minimun_theorem02: forall (x y: expr), |-- x --> (x --> y) --> y.
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

Lemma aux_minimun_theorem03: forall (x y z: expr), |--  y --> (x --> y --> z) --> (x --> z).
Proof.
  intros.
  pose proof aux_minimun_theorem00 x (y --> z) z.
  pose proof aux_minimun_theorem02 y z.
  eapply aux_minimun_rule02; eauto.
Qed.

Lemma aux_minimun_theorem04: forall (x y: expr), |-- (x --> x --> y) --> x --> y.
Proof.
  intros.
  pose proof axiom2 x (x --> y) y.
  pose proof aux_minimun_theorem02 x y.
  pose proof modus_ponens _ _ H H0.
  auto.
Qed.

Lemma provable_impp_arg_switch: forall (x y z: expr), |-- (x --> y --> z) --> (y --> x --> z).
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

Lemma provable_impp_trans: forall (x y z: expr), |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof provable_impp_arg_switch (y --> z) (x --> y) (x --> z).
  eapply modus_ponens; eauto. clear H.
  apply aux_minimun_theorem00.
Qed.

End DerivableRulesFromAxiomatization.

Section DerivableRules_multi_impp.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_multi_imp_shrink: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs (x --> y)) --> multi_imp xs (x --> y).
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

Lemma provable_multi_imp_arg_switch1: forall (xs: list expr) (x y: expr), |-- (x --> multi_imp xs  y) --> multi_imp xs (x --> y).
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

Lemma provable_multi_imp_arg_switch2: forall (xs: list expr) (x y: expr), |-- multi_imp xs (x --> y) --> (x --> multi_imp xs  y).
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

Lemma provable_multi_imp_weaken: forall (xs: list expr) (x y: expr), |-- x --> y -> |-- multi_imp xs x --> multi_imp xs y.
Proof.
  intros.
  induction xs.
  + auto.
  + apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_split:
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

Lemma provable_add_multi_imp_left_head: forall xs1 xs2 y, |-- multi_imp xs2 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1.
  + apply provable_impp_refl.
  + eapply aux_minimun_rule02; eauto.
    apply axiom1.
Qed.

Lemma provable_add_multi_imp_left_tail: forall xs1 xs2 y, |-- multi_imp xs1 y --> multi_imp (xs1 ++ xs2) y.
Proof.
  intros.
  induction xs1; simpl.
  + pose proof (provable_add_multi_imp_left_head xs2 nil y).
    rewrite app_nil_r in H; auto.
  + apply aux_minimun_rule01; auto.
Qed.

Lemma provable_multi_imp_modus_ponens: forall xs y z, |-- multi_imp xs y --> multi_imp xs (y --> z) --> multi_imp xs z.
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

End DerivableRules_multi_impp.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {AX: NormalAxiomatization L Gamma}.

Lemma Axiomatization2SequentCalculus_SC: NormalSequentCalculus L Gamma.
Proof.
  constructor.
  intros.
  rewrite derivable_provable.
  split; intros.
  + exists nil; split; auto.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    inversion H; subst.
    inversion H3.
Qed.

Context {minAX: MinimunAxiomatization L Gamma}.

Lemma Axiomatization2SequentCalculus_minSC: MinimunSequentCalculus L Gamma.
Proof.
  constructor.
  + intros.
    rewrite derivable_provable in H, H0 |- *.
    destruct H as [xs1 [? ?]], H0 as [xs2 [? ?]].
    exists (xs1 ++ xs2); split.
    - rewrite Forall_app_iff; auto.
    - pose proof modus_ponens _ _ (provable_add_multi_imp_left_tail xs1 xs2 _) H1.
      pose proof modus_ponens _ _ (provable_add_multi_imp_left_head xs1 xs2 _) H2.
      pose proof provable_multi_imp_modus_ponens (xs1 ++ xs2) x y.
      pose proof modus_ponens _ _ H5 H3.
      pose proof modus_ponens _ _ H6 H4.
      auto.
  + intros.
    rewrite derivable_provable in H |- *.
    destruct H as [xs [? ?]].
    pose proof provable_multi_imp_split _ _ _ _ H H0 as [xs1 [xs2 [? [? ?]]]].
    exists xs1.
    split; auto.
    eapply modus_ponens; [| exact H3].
    apply provable_multi_imp_weaken.
    clear - H2 minAX.
    induction H2.
    - apply axiom1.
    - inversion H; subst x0; clear H.
      simpl.
      pose proof aux_minimun_theorem04 x y.
      pose proof aux_minimun_rule01 _ _ x IHForall.
      eapply aux_minimun_rule02; [exact H0 | exact H].
Qed.

Lemma Axiomatization2SequentCalculus_bSC: BasicSequentCalculus L Gamma.
Proof.
  constructor.
  + intros.
    rewrite derivable_provable in H0 |- *.
    destruct H0 as [xs [? ?]].
    exists xs; split; auto.
    revert H0; apply Forall_impl.
    auto.
  + intros.
    rewrite derivable_provable.
    exists (x :: nil); split.
    - constructor; auto.
    - simpl.
      apply provable_impp_refl.
  + apply DeductionImpIntro_DeductionMP_2_DeductionSubst.
    - exact (@deduction_impp_intros _ _ _ Axiomatization2SequentCalculus_minSC).
    - exact (@deduction_modus_ponens _ _ _ Axiomatization2SequentCalculus_minSC).
Qed.

End Axiomatization2SequentCalculus.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Context {minL: MinimunLanguage L}
        {minSC: MinimunSequentCalculus L Gamma}.

Lemma deduction_impp_elim: forall Phi x y,
  Phi |-- impp x y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  eapply deduction_modus_ponens; solve_assum.
Qed.

Theorem deduction_theorem:
  forall (Phi: context) (x y: expr),
    Union _ Phi (Singleton _ x) |-- y <->
    Phi |-- x --> y.
Proof.
  intros; split.
  + apply deduction_impp_intros; auto.
  + apply deduction_impp_elim; auto.
Qed.

Lemma derivable_impp_refl: forall (Phi: context) (x: expr), Phi |-- x --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma deduction_left_impp_intros: forall (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- y --> x.
Proof.
  intros.
  apply deduction_theorem.
  solve_assum.
Qed.

Lemma derivable_axiom1: forall (Phi: context) (x y: expr),
  Phi |-- x --> y --> x.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  solve_assum.
Qed.

Lemma derivable_axiom2: forall (Phi: context) (x y z: expr),
  Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with y.
  + apply deduction_modus_ponens with x; solve_assum.
  + apply deduction_modus_ponens with x; solve_assum.
Qed.

Lemma derivable_modus_ponens: forall (Phi: context) (x y: expr),
  Phi |-- x --> (x --> y) --> y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with x; solve_assum.
Qed.

Lemma deduction_impp_trans: forall (Phi: context) (x y z: expr),
  Phi |-- x --> y ->
  Phi |-- y --> z ->
  Phi |-- x --> z.
Proof.
  intros.
  rewrite <- deduction_theorem in H |- *.
  apply deduction_modus_ponens with y; solve_assum.
Qed.

Lemma deduction_impp_arg_switch: forall (Phi: context) (x y z: expr),
  Phi |-- x --> y --> z ->
  Phi |-- y --> x --> z.
Proof.
  intros.
  rewrite <- !deduction_theorem in *.
  eapply deduction_weaken; [| exact H].
  intros ? ?.
  destruct H0; [destruct H0 |].
  + left; left; auto.
  + right; auto.
  + left; right; auto.
Qed.

End DerivableRulesFromSequentCalculus.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {Gamma: ProofTheory L}
        {minL: MinimunLanguage L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}.

Theorem SequentCalculus2Axiomatization_minAX: MinimunAxiomatization L Gamma.
Proof.
  constructor.
  + intros x y.
    rewrite !provable_derivable.
    intros.
    eapply deduction_modus_ponens; eauto.
  + intros x y.
    rewrite provable_derivable.
    apply derivable_axiom1.
  + intros x y z.
    rewrite provable_derivable.
    apply derivable_axiom2.
Qed.

End SequentCalculus2Axiomatization.

Definition Build_AxiomaticProofTheory {L: Language} {minL: MinimunLanguage L} (Provable: expr -> Prop): ProofTheory L :=
  Build_ProofTheory L Provable
   (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ Provable (multi_imp xs y)).

Definition Build_AxiomaticProofTheory_AX {L: Language} {minL: MinimunLanguage L} (Provable: expr -> Prop): NormalAxiomatization L (Build_AxiomaticProofTheory Provable) :=
  Build_NormalAxiomatization L minL (Build_AxiomaticProofTheory Provable) (fun _ _ => iff_refl _).

Definition Build_SequentCalculus {L: Language} (Derivable: context -> expr -> Prop): ProofTheory L :=
  Build_ProofTheory L (fun x => Derivable (Empty_set _) x) Derivable.

Definition Build_SequentCalculus_SC {L: Language} (Derivable: context -> expr -> Prop): NormalSequentCalculus L (Build_SequentCalculus Derivable) :=
  Build_NormalSequentCalculus L (Build_SequentCalculus Derivable) (fun _ => iff_refl _).

Definition OpaqueProp (P: Prop): Prop := P.

Lemma MakeSequentCalculus_MinimunAxiomatization: forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} (P: Prop),
  OpaqueProp
  (NormalAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma)) ->
   MinimunAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma)) ->
   NormalSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)) ->
   BasicSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)) ->
   MinimunSequentCalculus L (Build_AxiomaticProofTheory (@provable L Gamma)) ->
   P) <->
  (Basics.impl (MinimunAxiomatization L Gamma) P).
Proof.
  unfold OpaqueProp.
  intros.
  split; intros.
  + intro.
    assert (NormalAxiomatization L (Build_AxiomaticProofTheory provable))
      by (apply Build_AxiomaticProofTheory_AX).
    assert (MinimunAxiomatization L (Build_AxiomaticProofTheory provable))
      by (destruct H0; constructor; auto).
    assert (NormalSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_SC).
    assert (BasicSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_bSC).
    assert (MinimunSequentCalculus L (Build_AxiomaticProofTheory provable))
      by (apply Axiomatization2SequentCalculus_minSC).
    apply H; auto.
  + apply H.
    destruct H1; constructor; auto.
Qed.

Hint Rewrite <- @MakeSequentCalculus_MinimunAxiomatization: AddSC.

Ltac addSC_revert_dep T :=
  match goal with
  | H: context [T] |- ?G =>
      match type of H with
      | ?HH =>
          first [ revert H; change (Basics.impl HH G);
                  (progress autorewrite with AddSC || fail 1000)
                | addSC_revert_dep H];
          addSC_revert_dep T;
          unfold OpaqueProp at 1;
          intros
      end
  | _ => idtac
  end.

Ltac AddSequentCalculus Gamma :=
  addSC_revert_dep Gamma;
  let Gamma' := fresh "Gamma" in
  change (@provable _ Gamma) with (@provable _ (Build_AxiomaticProofTheory provable));
  set (Gamma' := (Build_AxiomaticProofTheory provable)) in *;
  clearbody Gamma';
  clear Gamma;
  rename Gamma' into Gamma.

Section DerivableRulesFromAxiomatization'.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Lemma provable_impp_refl': forall (x: expr), |-- x --> x.
Proof.
  AddSequentCalculus Gamma.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  solve_assum.
Abort.

End DerivableRulesFromAxiomatization'.