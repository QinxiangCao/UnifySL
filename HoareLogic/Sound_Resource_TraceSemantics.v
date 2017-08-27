Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_TraceSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.
(*
Lemma thread_local_state_enable_acq_inv {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac}:
  forall Inv r s1 A1 A2 ms,
    (forall r0 : resource, A1 r0 \/ r = r0 <-> A2 r0) ->
    ~ A1 r ->
    thread_local_state_enable Inv (Aacquire_res r) (A1, s1) ms ->
    exists s2 I f, Inv (r, I) /\ I f /\ join s1 f s2 /\ ms = Terminating (A2, s2).
Proof.
  intros.
  inversion H1; subst.
  + apply Aacquire_res_inv in H2; subst.
    exists n, I, f.
    split; [| split; [| split]]; auto.
    f_equal.
    f_equal.
    extensionality r0; apply prop_ext.
    specialize (H5 r0); specialize (H r0); tauto.
  + symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2.
  + symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2.
  + exfalso; apply H2; exists r; auto.
Qed.

Lemma thread_local_state_enable_rel_inv {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac}:
  forall Inv r s1 A1 A2 ms,
    (forall r0 : resource, A2 r0 \/ r = r0 <-> A1 r0) ->
    ~ A2 r ->
    thread_local_state_enable Inv (Arelease_res r) (A1, s1) ms ->
    exists I, Inv (r, I) /\ 
    ((ms = Error /\ forall s2, ~ exists f, I f /\ join s2 f s1) \/
     (exists s2, greatest (fun s2 => exists f, I f /\ join s2 f s1) s2 /\ ms = Terminating (A2, s2))).
Proof.
  intros.
  inversion H1; subst.
  + apply Aacquire_Arelease_res in H2; inversion H2.
  + apply Arelease_res_inv in H2; subst.
    exists I; split; auto.
    right; exists n.
    split; auto.
    f_equal.
    f_equal.
    extensionality r0; apply prop_ext.
    specialize (H5 r0); specialize (H r0).
    assert (r = r0 -> ~ A3 r0) by (intro; subst; auto).
    assert (r = r0 -> ~ A2 r0) by (intro; subst; auto).
    tauto.
  + apply Arelease_res_inv in H2; subst.
    exists I; split; auto.
  + exfalso; apply H2; exists r; auto.
Qed.
*)
Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {MD: Model}
        {J: Join model}
        {SA: SeparationAlgebra model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {DCSA: DownwardsClosedSeparationAlgebra model}
        {UCSA: UpwardsClosedSeparationAlgebra model}
        {Res: Resource}
        {Ac: Action}
        {Acr: Action_resource Ac Res}
        {nAcr: NormalAction_resource Ac Res}
        {TS: TraceSemantics P (resources * model) Ac}
        {AIr: ActionInterpret_resource model Ac Res ac_sem}
        {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (fun a => ~ is_resource_action a)}
        {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.

Instance KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) (fun a => ~ is_resource_action a) :=
  ordered_and_frame_AIr _ _ _.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := {
  at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2;
  invariant_mono: forall r I,  Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2;
  invariant_precise: forall r I, Inv (r, I) -> forall s,
    (exists s', (fun s' => exists f, I f /\ join s' f s) s') ->
    (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s')
}.
(*
Definition ThreadLocal_KSA_AIr: forall (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}, @KSAActionInterpret_resource (resources * model) Ac (ThreadLocal_ActionInterpret_resource ac_sem Inv) (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R).
  Check @lift_join.
 *)

Lemma ThreadLocal_ordered_frame_property (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}: forall (a: action) (m1 f n1' n1: resources * model) (n2: MetaState (resources * model)) fst_m2
    (ASSU: res_enable a (fst m1) fst_m2 (fst f) (*forall r, a = Arelease_res r -> ~ fst f r*)),
    @join _ (prod_Join _ _) m1 f n1' ->
    (RelProd (discPred_R _) R) n1' n1 ->
    thread_local_state_enable Inv a n1 n2  ->
    exists m2 n2', @lift_join _ (prod_Join _ _) m2 (Terminating f) n2' /\ @Partial.forward _ (RelProd (discPred_R _) R) n2' n2 /\ match m2 with Terminating m2 => fst m2 = fst_m2 | _ => True end /\ thread_local_state_enable Inv a m1 m2.
Proof.
  intros.
  destruct (classic (is_resource_action a)) as [[?r [? | ?]] | ?].
  + subst a.
    inversion H1; subst.
    Focus 2. { symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2. } Unfocus.
    Focus 2. { symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2. } Unfocus.
    Focus 2. { exfalso; apply H2; exists r; auto. } Unfocus.
    apply Aacquire_res_inv in H2; subst.
    rename m into n1, n into n2.
    destruct n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
    hnf in H; simpl in H; destruct H.
    hnf in H0; simpl in H0. destruct H0. hnf in H0, H7; simpl in H0, H7.
    pose proof join_Korder_down _ _ _ _ _ H6 H7 ltac:(reflexivity) as [n2' [? ?]].
    pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H2) H8 as [m2 [? ?]].
    assert (A1 = A1').
    Focus 1. {
      extensionality r0; apply prop_ext.
      apply iff_sym, H0.
    } Unfocus.
    subst A1'.
    pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H) H3 as [B2 [? ?]].
    exists (Terminating (B2, m2)), (Terminating (A2, n2')).
    split; [| split; [| split]].
    - constructor.
      split; apply join_comm; auto.
    - constructor; split; auto; simpl.
      hnf; intro; simpl; hnf; tauto.
    - apply res_enable_acq_inv in ASSU.
      simpl in ASSU; destruct ASSU as [? _].
      simpl; clear - H14 H12.
      extensionality r0; apply prop_ext.
      specialize (H12 r0); specialize (H14 r0); destruct H12, H14; tauto.
    - simpl.
      eapply thread_local_state_enable_acq; eauto.
  + subst a.
    destruct n1 as [A1 n1], n1' as [A1' n1'], f as [Af f], m1 as [B1 m1].
    hnf in H; simpl in H; destruct H.
    hnf in H0; unfold RelCompFun in H0; simpl in H0; destruct H0.
    assert (A1' = A1).
    Focus 1. {
      extensionality r0; apply prop_ext.
      apply H0.
    } Unfocus.
    subst A1'; clear H0.
    (*
    assert (RES: exists B2, join B2 (eq r) B1 /\ forall A2, join A2 (eq r) A1 -> join B2 Af A2).
    Focus 1. {
      assert (A1 r).
      + inversion H1; subst.
        - apply Aacquire_Arelease_res in H0; inversion H0.
        - apply Arelease_res_inv in H0; subst.
          specialize (H6 r); destruct H6; tauto.
        - apply Arelease_res_inv in H0; subst.
          specialize (H6 r); destruct H6; tauto.
        - exfalso; apply H0; exists r; auto.
      + clear - H H0 ASSU nAcr.
        apply res_enable_rel_inv in ASSU; simpl in ASSU.
        exists fst_m2.
        split; auto.
        intros.
        - intros r0.
          specialize (H r0).
          destruct H.
          assert (r = r0 -> ~ Af r0) by (intro; subst; auto).
          assert (r = r0 -> A1 r0) by (intro; subst; auto).
          split; tauto.
        - intros.
          intros r0.
          specialize (H r0).
          specialize (H1 r0).
          destruct H, H1.
          assert (r = r0 -> ~ Af r0) by (intro; subst; auto).
          assert (r = r0 -> A1 r0) by (intro; subst; auto).
          split; tauto.
    } Unfocus.
    *)
    destruct (classic (forall I, Inv (r, I) -> exists m2, (fun m2 => exists f, I f /\ join m2 f m1) m2)).
    - inversion H1; subst.
      Focus 1. { apply Aacquire_Arelease_res in H4; inversion H4. } Unfocus.
      Focus 2. {
        exfalso.
        apply Arelease_res_inv in H4; subst.
        specialize (H0 _ H8).
        destruct H0 as [m2 [f0 [? ?]]].
        pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H4) H2 as [n2' [? ?]].
        pose proof join_Korder_up _ _ _ _ H6 H3 as [_f0 [n2 [? [? ?]]]].
        apply (H10 n2); clear H10.
        exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto].
      } Unfocus.
      Focus 2. { exfalso; apply H4; exists r; auto. } Unfocus.
      apply Arelease_res_inv in H4; subst.
      specialize (H0 _ H8).
      apply (invariant_precise _ _ H8) in H0.
      destruct H0 as [m2 ?].
      destruct (proj1 H0) as [f0 [? ?]].
      pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H5) H2 as [n2' [? ?]].
      pose proof join_Korder_up _ _ _ _ H9 H3 as [_f0 [_n2 [? [? ?]]]].
      assert ((fun n : model => exists f : model, I f /\ join n f n1) _n2).
      Focus 1. { exists _f0; split; [eapply (invariant_mono _ _ H8); eauto | apply join_comm; auto]. } Unfocus.
      apply (proj2 H10) in H14.
      apply res_enable_rel_inv in ASSU; simpl in ASSU.
      rename fst_m2 into B2.
      exists (Terminating (B2, m2)), (Terminating (A2, n2')).
      split; [| split; [| split]].
      * constructor.
        split; auto.
        simpl.
        clear - ASSU H H7.
        intros r0; specialize (ASSU r0); specialize (H r0); specialize (H7 r0).
        destruct ASSU, H, H7; split; tauto.
      * constructor.
        split; [hnf; intros ?; hnf; tauto | change (n2' <= n); etransitivity; eauto].
      * auto.
      * simpl.
        eapply thread_local_state_enable_rel_succ; eauto.
    - exists Error, n2.
      split; [| split; [| split]].
      * constructor.
      * destruct n2; constructor.
        destruct p as [A2 n2].
        split; [hnf; intros ?; hnf; tauto | change (n2 <= n2); reflexivity].
      * auto.
      * apply Classical_Pred_Type.not_all_ex_not in H0; destruct H0 as [I ?].
        apply imply_to_and in H0; destruct H0.
        apply res_enable_rel_inv in ASSU; simpl in ASSU.
        eapply thread_local_state_enable_rel_fail; eauto.
  + rewrite <- (thread_local_state_enable_non_resource_action Inv) in H1 by auto.
    change ((fun a => ~ is_resource_action a) a) in H2.
    pose proof ordered_frame_property _ _ _ _ _ _ H2 H H0 H1 as [m2 [n2' [? [? ?]]]].
    exists m2, n2'.
    split; [| split; [| split]]; auto.
    - apply res_enable_not_res_inv in ASSU; auto.
      destruct m1 as [A1 m1], m2 as [| | [A2 m2]]; auto.
      simpl in H5.
      apply state_enable_non_resource_action in H5; auto.
      subst; auto.
    - simpl.
      rewrite <- (thread_local_state_enable_non_resource_action Inv) by auto.
      auto.
Qed.

Lemma hoare_parallel_partial_sound
      {CPP: ConcurrentProgrammingLanguage_Sparallel P}
      {AcP: Action_Parallel Ac}
      {nAcPr: NormalAction_Parallel_resource Ac Res}
      {c2tP: Command2Traces_Sparallel_resource P model Ac Res c2t}
      {AIPr: ActionInterpret_Parallel_resource model Ac Res ac_sem}:
  forall Inv c1 P1 Q1 c2 P2 Q2 (INV: LegalInvariants Inv),
  guarded_triple_partial_valid Inv P1 c1 Q1 ->
  guarded_triple_partial_valid Inv P2 c2 Q2 ->
  guarded_triple_partial_valid Inv (P1 * P2) (Sparallel c1 c2) (Q1 * Q2).
Proof.
  intros.
  rename H into LEFT_ASSU, H0 into RIGHT_ASSU.
  hnf in LEFT_ASSU, RIGHT_ASSU |- *; intros.
  unfold access, ThreadLocal_BSS in LEFT_ASSU, RIGHT_ASSU, H0; simpl in LEFT_ASSU, RIGHT_ASSU, H0.
  inversion H0; subst; clear H0.
  rewrite Sparallel_denote in H1.
  set (Tr1 := cmd_denote c1) in LEFT_ASSU, H1.
  set (Tr2 := cmd_denote c2) in RIGHT_ASSU, H1.
  clearbody Tr1 Tr2; clear c1 c2.
  inversion H1; subst; clear H1.
  set (A1 := fun _: resource => False) in LEFT_ASSU at 1, H4 at 1.
  set (A2 := fun _: resource => False) in RIGHT_ASSU at 1, H4 at 1.
  set (A := fun _: resource => False) in H2 at 1.
  rewrite sat_sepcon in H.
  destruct H as [s1 [s2 [? [? ?]]]].
  set (s0 := s_pre) in H.
  assert (STATE_JOIN: @join _ (prod_Join resources model) (A1, s1) (A2, s2) (A, s0)).
  Focus 1. {
    split; auto.
    hnf; intros r0.
    simpl; subst A1 A2 A; split; tauto.
  } Unfocus.
  assert (STATE_LE: @Krelation _ (RelProd (discPred_R resource) R) (A, s0) (A, s_pre)).
  Focus 1. {
    split; hnf; simpl.
    + intros; hnf; tauto.
    + change (s_pre <= s_pre).
      reflexivity.
  } Unfocus.
  clearbody A1 A2 A s0. clear H.
  specialize (fun ms_post HH => LEFT_ASSU s1 ms_post H1 (traces_access_intro tr1 _ _ _ H0 HH)).
  specialize (fun ms_post HH => RIGHT_ASSU s2 ms_post H5 (traces_access_intro tr2 _ _ _ H3 HH)).
  clear P1 P2 H1 H5 Tr1 Tr2 H0 H3.
  rename H2 into TRACE_ACC.
  revert s0 s1 s2 s_pre A LEFT_ASSU RIGHT_ASSU STATE_JOIN STATE_LE TRACE_ACC; induction H4; intros.
  + inversion TRACE_ACC; subst.
    destruct ms_post; subst; inversion H.
    subst m A.
    assert (A2 = fun _ => False).
    Focus 1. {
      extensionality r; apply prop_ext.
      destruct STATE_JOIN as [? _].
      hnf in H0. specialize (H0 r).
      simpl in H0; destruct H0.
      tauto.
    } Unfocus.
    assert (A1 = fun _ => False).
    Focus 1. {
      extensionality r; apply prop_ext.
      destruct STATE_JOIN as [? _].
      hnf in H1. specialize (H1 r).
      simpl in H1; destruct H1.
      tauto.
    } Unfocus.
    subst A1 A2.
    specialize (LEFT_ASSU (Terminating s1) (trace_access_nil _)); simpl in LEFT_ASSU.
    specialize (RIGHT_ASSU (Terminating s2) (trace_access_nil _)); simpl in RIGHT_ASSU.
    eapply sat_mono; [exact (proj2 STATE_LE) |].
    rewrite sat_sepcon.
    exists s1, s2.
    split; [| split]; auto.
    exact (proj2 STATE_JOIN).
  + exfalso.
    destruct (res_actions_no_race _ _ H).
    apply (state_enable_race_actions_spec a1 a2 A1 A2 s1 s2 s0); auto.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
      specialize (LEFT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
      inversion LEFT_ASSU.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H2 by auto.
      specialize (RIGHT_ASSU Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H2)).
      inversion RIGHT_ASSU.
    - exact (proj2 STATE_JOIN).
  + change (res_enable a1 (fst (A1, s1)) A1' (fst (A2, s2))) in H.
    inversion TRACE_ACC; subst.
    - (* NonTerminating *)
      destruct ms_post; inversion H5; clear H5; auto.
    - (* Error *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A1' H STATE_JOIN STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      simpl lift_function in H2.
      exfalso.
      apply (LEFT_ASSU Error).
      apply trace_access_Error; auto.
    - (* Terminating *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A1' H STATE_JOIN STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
      destruct n2' as [| | n2']; inversion H1; subst.
      destruct m2 as [| | m2]; inversion H0; subst.
      * exfalso.
        apply (LEFT_ASSU Error).
        apply trace_access_Error; auto.
      * destruct s' as [A' s'], m2 as [A1' s1'], n2' as [A0' s0'].
        assert (A0' = A').
        Focus 1. {
          clear - H9. destruct H9 as [? _]; hnf in H; simpl in H.
          extensionality r0; apply prop_ext; apply H.
        } Unfocus.
        subst A0'.
        apply (IHtrace_interleave s0' s1' s2 s' A'); auto.
        intros.
        apply LEFT_ASSU.
        eapply trace_access_Terminating; eauto.
  + change (res_enable a2 (fst (A2, s2)) A2' (fst (A1, s1))) in H.
    inversion TRACE_ACC; subst.
    - (* NonTerminating *)
      destruct ms_post; inversion H5; clear H5; auto.
    - (* Error *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ Error A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H3 as [Error' [Error'' [? [? [_ ?]]]]].
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      simpl lift_function in H2.
      exfalso.
      apply (RIGHT_ASSU Error).
      apply trace_access_Error; auto.
    - (* Terminating *)
      pose proof ThreadLocal_ordered_frame_property Inv _ _ _ _ _ (Terminating s') A2' H (@join_comm _ _ (prod_SA _ _) _ _ _ STATE_JOIN) STATE_LE H2 as [m2 [n2' [? [? [? ?]]]]].
      destruct n2' as [| | n2']; inversion H1; subst.
      destruct m2 as [| | m2]; inversion H0; subst.
      * exfalso.
        apply (RIGHT_ASSU Error).
        apply trace_access_Error; auto.
      * destruct s' as [A' s'], m2 as [A2' s2'], n2' as [A0' s0'].
        assert (A0' = A').
        Focus 1. {
          clear - H9. destruct H9 as [? _]; hnf in H; simpl in H.
          extensionality r0; apply prop_ext; apply H.
        } Unfocus.
        subst A0'.
        apply (IHtrace_interleave s0' s1 s2' s' A'); auto.
        intros.
        apply RIGHT_ASSU.
        eapply trace_access_Terminating; eauto.
        apply (@join_comm _ _ (prod_SA _ _)); auto.
Qed.

End soundness.
