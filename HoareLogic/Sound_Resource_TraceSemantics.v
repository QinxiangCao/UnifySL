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
        {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J)}
        {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.

Definition KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) :=
  ordered_and_frame_AIr _ _.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := {
  at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2;
  invariant_mono: forall r I,  Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2;
  invariant_precise: forall r I, Inv (r, I) -> forall s,
    (exists s', (fun s' => exists f, I f /\ join s' f s) s') ->
    (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s')
}.

Definition ThreadLocal_KSA_AIr: forall (Inv: resource * (model -> Prop) -> Prop) {INV: LegalInvariants Inv}, @KSAActionInterpret_resource (resources * model) Ac (ThreadLocal_ActionInterpret_resource ac_sem Inv) (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R).
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
    split; [| split].
    - constructor.
      split; apply join_comm; auto.
    - constructor; split; auto; simpl.
      hnf; intro; simpl; hnf; tauto.
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
  + inversion TRACE_ACC; subst.
    - (* NonTerminating *)
      destruct ms_post; inversion H5; clear H5; auto.
    - (* Error *)
      pose proof @ordered_frame_property _ _ _ _ _ _ _ (ThreadLocal_KSA_AIr Inv) _ _ (fun _ => False) _ _ _ _ Error STATE_JOIN STATE_LE H3 as [Error' [Error'' [? [? ?]]]].
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      simpl lift_function in H2.
      exfalso.
      apply (LEFT_ASSU Error).
      apply trace_access_Error. Set Printing All. simpl in H2 |- *. exact H2. simpl. simpl in H2.
      Abort.
End soundness.