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
        {SAAIr: SAActionInterpret_resource model Ac Res ac_sem}
        {KSA_AIr: KSAActionInterpret_resource model Ac Res ac_sem}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := {
  at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2;
  invariant_mono: forall r I,  Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2;
  invariant_precise: forall r I, Inv (r, I) -> forall s,
    (exists s', (fun s' => exists f, I f /\ join s' f s) s') ->
    (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s')
}.

Definition ThreadLocal_KSA_AIr: forall (Inv: resource * (model -> Prop) -> Prop) {LEGAL: LegalInvariants Inv}, KSAActionInterpret_resource model Ac Res (ThreadLocal_ActionInterpret_resource ac_sem Inv).
  intros.
  constructor.
  intros.
  destruct (classic (is_resource_action a)) as [[?r [? | ?]] | ?].
  + subst a.
    simpl in H1.
    inversion H1; subst.
    Focus 2. { symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2. } Unfocus.
    Focus 2. { symmetry in H2; apply Aacquire_Arelease_res in H2; inversion H2. } Unfocus.
    Focus 2. { exfalso; apply H2; exists r; auto. } Unfocus.
    apply Aacquire_res_inv in H2; subst.
    destruct n2 as [| | n2]; inversion H5; subst; clear H5.
    pose proof join_Korder_down _ _ _ _ _ H10 H0 ltac:(reflexivity) as [n2' [? ?]].
    pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H) H2 as [m2 [? ?]].
    exists (Terminating m2), (Terminating n2').
    split; [| split].
    - constructor; apply join_comm; auto.
    - constructor; auto.
    - simpl.
      eapply thread_local_state_enable_acq; eauto.
  + subst a.
    simpl in H1.
    assert (RES: A1 r).
    Focus 1. {
      inversion H1; subst.
      + apply Aacquire_Arelease_res in H2; inversion H2.
      + apply Arelease_res_inv in H2; subst.
        specialize (H6 r); tauto.
      + apply Arelease_res_inv in H2; subst.
        specialize (H6 r); tauto.
      + exfalso; apply H2; exists r; auto.
    } Unfocus.
    destruct (classic (forall I, Inv (r, I) -> exists m2, (fun m2 => exists f, I f /\ join m2 f m1) m2)).
    - inversion H1; subst.
      Focus 1. { apply Aacquire_Arelease_res in H3; inversion H3. } Unfocus.
      Focus 2. {
        exfalso.
        apply Arelease_res_inv in H3; subst.
        destruct n2; inversion H6; subst; clear H6.
        specialize (H2 _ H9).
        destruct H2 as [m2 [f0 [? ?]]].
        pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H3) H as [n2' [? ?]].
        pose proof join_Korder_up _ _ _ _ H5 H0 as [_f0 [n2 [? [? ?]]]].
        apply (H10 n2); clear H10.
        exists _f0; split; [eapply (invariant_mono _ _ H9); eauto | apply join_comm; auto].
      } Unfocus.
      Focus 2. { exfalso; apply H3; exists r; auto. } Unfocus.
      apply Arelease_res_inv in H3; subst.
      destruct n2 as [| | n2]; inversion H6; subst; clear H6.
      specialize (H2 _ H9).
      apply (invariant_precise _ _ H9) in H2.
      destruct H2 as [m2 ?].
      destruct (proj1 H2) as [f0 [? ?]].
      pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H4) H as [n2' [? ?]].
      pose proof join_Korder_up _ _ _ _ H6 H0 as [_f0 [_n2 [? [? ?]]]].
      assert ((fun n : model => exists f : model, I f /\ join n f n1) _n2).
      Focus 1. { exists _f0; split; [eapply (invariant_mono _ _ H9); eauto | apply join_comm; auto]. } Unfocus.
      apply (proj2 H10) in H14.
      exists (Terminating m2), (Terminating n2').
      split; [| split].
      * constructor; auto.
      * constructor. etransitivity; eauto.
      * simpl.
        eapply thread_local_state_enable_rel_succ; eauto.
    - exists Error, n2.
      split; [| split].
      * constructor.
      * destruct n2; constructor.
        reflexivity.
      * simpl.
        apply Classical_Pred_Type.not_all_ex_not in H2; destruct H2 as [I ?].
        apply imply_to_and in H2; destruct H2.
        clear A2 H1.
        set (A2 := fun r0 => A1 r0 /\ r <> r0).
        assert (forall r0, A2 r0 \/ r = r0 <-> A1 r0).
        Focus 1. {
          intros.
          assert (r = r0 -> A1 r0) by (intros; subst; auto).
          subst A2; tauto.
        } Unfocus.
        assert (~ A2 r).
        Focus 1. {
          subst A2; intro.
          tauto.
        } Unfocus.
        eapply thread_local_state_enable_rel_fail; eauto.
  + simpl in H1.
    rewrite <- (thread_local_state_enable_non_resource_action Inv) in H1 by auto.
    pose proof ordered_frame_property _ _ _ _ _ _ _ _ H H0 H1 as [m2 [n2' [? [? ?]]]].
    exists m2, n2'.
    split; [| split]; auto.
    simpl.
    rewrite <- (thread_local_state_enable_non_resource_action Inv) by auto.
    auto.
Qed.
(*
Lemma Sparallel_sound_acq_aux: forall Inv r tr s A A' ms,
  @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) (Aacquire_res r :: tr) (s, A) ms ->
  (forall r0, A r0 \/ r = r0 <-> A' r0) ->
  ~ A r ->
  exists s' I f,
    Inv (r, I) /\ I f /\ join s f s' /\ @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) tr (s', A') ms.
Proof.
  intros.
  apply (@trace_access_Terminating_inv _ _ (ThreadLocal_ActionInterpret_resource _ Inv) (fun sa => exists s' I f, Inv (r, I) /\ I f /\ join s f s' /\ sa = (s', A'))) in H.
  + destruct H as [ms' [[s' [I [f [? [? [? HEQ]]]]]] ?]]; subst ms'.
    exists s', I, f; auto.
  + intros.
    simpl in H2.
    eapply thread_local_state_enable_acq_inv in H2; auto.
    destruct H2 as [s' [I [f [? [? [? ?]]]]]].
    exists (s', A').
    split; [| exact H5].
    exists s', I, f; auto.
Qed.

Lemma acq_assoc_aux: forall s1 s2 s0 s f s',
  join s1 s2 s0 ->
  s0 <= s ->
  join s f s' ->
  exists s1' s0',
    join s1' s2 s0' /\
    s0' <= s' /\
    join s1 f s1'.
Proof.
  intros.
  pose proof join_Korder_down _ _ _ _ _ H1 H0 ltac:(reflexivity) as [s0' [? ?]].
  pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H) H2 as [s1' [? ?]].
  exists s1', s0'.
  split; [| split]; auto.
  apply join_comm; auto.
Qed.

Lemma Sparallel_sound_rel_aux: forall Inv r tr s A A' ms,
  @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) (Arelease_res r :: tr) (s, A) ms ->
  (forall r0, A' r0 \/ r = r0 <-> A r0) ->
  ~ A' r ->
  exists I, Inv (r, I) /\
    ((forall s', ~ exists f, I f /\ join s' f s) \/
     (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s' /\ @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) tr (s', A') ms)).
Proof.
  intros.
  inversion H; subst.
  + simpl in H6.
    eapply thread_local_state_enable_rel_inv in H6; auto.
    destruct H6 as [? [? [[? ?] | [? [? ?]]]]]; congruence.
  + simpl in H6.
    eapply thread_local_state_enable_rel_inv in H6; auto.
    destruct H6 as [I [? [[? ?] | [? [? ?]]]]]; [| congruence].
    exists I; split; auto.
  + simpl in H4.
    eapply thread_local_state_enable_rel_inv in H4; auto.
    destruct H4 as [I [? [[? ?] | [s'' [? ?]]]]]; [congruence |].
    inversion H4; subst; clear H4.
    exists I; split; auto.
    right; exists s''; auto.
Qed.

Lemma rel_fail_assoc_aux: forall s1 s2 s0 s s1' f1,
  join s1 s2 s0 ->
  s0 <= s ->
  join s1' f1 s1 ->
  exists s' f, join s' f s /\ f1 <= f.
Proof.
  intros.
  pose proof join_assoc _ _ _ _ _ (join_comm _ _ _ H1) H as [s0' [? ?]].
  pose proof join_Korder_up _ _ _ _ H3 H0 as [f [s' [? [? ?]]]].
  exists s', f.
  split; auto.
  apply join_comm; auto.
Qed.
*)
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
  assert (RES_JOIN: forall r, A1 r \/ A2 r <-> A r) by (intro; subst A1 A2 A; simpl; tauto).
  assert (RES_DISJ: forall r, A1 r -> A2 r -> False) by (intro; subst A1 A2; simpl; tauto).
  clearbody A1 A2 A.
  
  rewrite sat_sepcon in H.
  destruct H as [s1 [s2 [STATE_JOIN [? ?]]]].
  set (s0 := s_pre) in STATE_JOIN.
  assert (STATE_LE: s0 <= s_pre) by (subst s0; reflexivity).
  clearbody s0.
  specialize (fun ms_post HH => LEFT_ASSU s1 ms_post H (traces_access_intro tr1 _ _ _ H0 HH)).
  specialize (fun ms_post HH => RIGHT_ASSU s2 ms_post H1 (traces_access_intro tr2 _ _ _ H3 HH)).
  clear P1 P2 H H1 Tr1 Tr2 H0 H3.
  rename H2 into TRACE_ACC.
  revert s0 s1 s2 s_pre A LEFT_ASSU RIGHT_ASSU STATE_JOIN STATE_LE TRACE_ACC RES_JOIN RES_DISJ; induction H4; intros.
  + inversion TRACE_ACC; subst.
    destruct ms_post; subst; inversion H.
    subst m A.
    assert (A1 = fun _ => False) by (extensionality r; apply prop_ext; specialize (RES_JOIN r); tauto).
    assert (A2 = fun _ => False) by (extensionality r; apply prop_ext; specialize (RES_JOIN r); tauto).
    subst A1 A2.
    specialize (LEFT_ASSU (Terminating s1) (trace_access_nil _)); simpl in LEFT_ASSU.
    specialize (RIGHT_ASSU (Terminating s2) (trace_access_nil _)); simpl in RIGHT_ASSU.
    eapply sat_mono; [exact STATE_LE |].
    rewrite sat_sepcon.
    exists s1, s2.
    split; [| split]; auto.
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
  +

(*

        destruct (classic (is_resource_action a1)) as [[?r [? | ?]] | ?].
    - subst a1.
      destruct (res_enable_acq_inv _ _ _ _ H) as [? [? ?]].
      set (A' := fun r0 => A r0 \/ r = r0).
      destruct (Sparallel_sound_acq_aux Inv r tr s_pre A A' _ TRACE_ACC) as [s' [I [f ?]]].
      1: subst A'; intro; apply iff_refl.
      1: clear - RES_JOIN H1 H2; firstorder.

      clear TRACE_ACC; destruct H3 as [? [? [JOIN_F TRACE_ACC]]].
      pose proof acq_assoc_aux _ _ _ _ _ _ STATE_JOIN STATE_LE JOIN_F as [s1' [s0' [? [? ?]]]].
      apply (IHtrace_interleave s0' s1' s2 s' A').
      * intros.
        apply LEFT_ASSU.
        eapply trace_access_Terminating; [clear HH | exact HH].
        simpl.
        eapply thread_local_state_enable_acq; eassumption.
      * apply RIGHT_ASSU.
      * auto.
      * auto.
      * exact TRACE_ACC.
      * intros.
        clear - RES_JOIN H0; subst A'; firstorder.
      * intro.
        assert (r = r0 -> ~ A2 r0) by (intros; subst; auto).
        specialize (RES_DISJ r0); specialize (H0 r0).
        tauto.
    - subst a1.
      destruct (res_enable_rel_inv _ _ _ _ H) as [? ?].
      set (A' := fun r0 => A1' r0 \/ A2 r0).
      assert (forall I, Inv (r, I) -> exists s1', greatest (fun s1' => exists f, I f /\ join s1' f s1) s1').
      Focus 1. {
        intros.
        apply (invariant_precise r); auto.
        apply NNPP.
        intro.
        apply (LEFT_ASSU Error).
        apply trace_access_Error.
        simpl.
        apply (thread_local_state_enable_rel_fail _ _ A1 A1' I); auto.
        intros s1' [f [? ?]].
        apply H3; exists s1', f; auto.
      } Unfocus.
      destruct (Sparallel_sound_rel_aux Inv r tr s_pre A A' _ TRACE_ACC) as [I [? [? | [s' [? ?]]]]].
      1: subst A'; intro; specialize (H0 r0); specialize (RES_JOIN r0); tauto.
      1: subst A'; intro; specialize (H0 r); specialize (RES_DISJ r); tauto.

      Focus 1. { (* fail case *)
        exfalso.
        specialize (H2 _ H3).
        destruct H2 as [s1' [? _]].
        destruct H2 as [f1 [? ?]].
        pose proof rel_fail_assoc_aux _  _ _ _ _ _ STATE_JOIN STATE_LE H6 as [s' [f [? ?]]].
        apply (H5 s'); clear H5.
        exists f; split; auto.
        eapply invariant_mono; eassumption.
      } Unfocus.
      
      clear TRACE_ACC; rename H6 into TRACE_ACC.
      specialize (H2 _ H3).
      destruct H2 as [s1' [? _]].
      (*
      apply (IHtrace_interleave s1' s2 s' A').
      * intros.
        apply LEFT_ASSU.
        eapply trace_access_Terminating; [clear HH | exact HH].
        simpl.
        eapply thread_local_state_enable_rel_succ; eassumption.
      * apply RIGHT_ASSU.
      * apply join_comm; auto.
      * exact TRACE_ACC.
      * intros.
        clear - RES_JOIN H0; subst A'; firstorder.
      * intro.
        assert (r = r0 -> ~ A2 r0) by (intros; subst; auto).
        specialize (RES_DISJ r0); specialize (H0 r0).
        tauto.
       *) *)
      Abort.
End soundness.