Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
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

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {MD: Model}
        {J: Join model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {Res: Resource}
        {Ac: Action}
        {Acr: Action_resource Ac Res}
        {TS: TraceSemantics P (model * resources) Ac}
        {SAAIr: SAActionInterpret_resource model Ac Res ac_sem}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Lemma hoare_parallel_partial_sound
      {CPP: ConcurrentProgrammingLanguage_Sparallel P}
      {AcP: Action_Parallel Ac}
      {nAcPr: NormalAction_Parallel_resource Ac Res}
      {c2tP: Command2Traces_Sparallel_resource P model Ac Res c2t}
      {AIPr: ActionInterpret_Parallel_resource model Ac Res ac_sem}:
  forall Inv c1 P1 Q1 c2 P2 Q2,
  guarded_triple_partial_valid Inv P1 c1 Q1 ->
  guarded_triple_partial_valid Inv P2 c2 Q2 ->
  guarded_triple_partial_valid Inv (P1 * P2) (Sparallel c1 c2) (Q1 * Q2).
Proof.
  intros.
  hnf in H, H0 |- *; intros.
  unfold access, ThreadLocal_BSS in H, H0, H2; simpl in H, H0, H2.
  inversion H2; subst; clear H2.
  rewrite Sparallel_denote in H3.
  set (Tr1 := cmd_denote c1) in H, H3.
  set (Tr2 := cmd_denote c2) in H0, H3.
  clearbody Tr1 Tr2; clear c1 c2.
  inversion H3; subst; clear H3.
  set (A1 := fun _: resource => False) in H at 1, H6 at 1.
  set (A2 := fun _: resource => False) in H0 at 1, H6 at 1.
  set (A := fun _: resource => False) in H4 at 1.
  assert (forall r, A1 r \/ A2 r <-> A r) by (intro; subst A1 A2 A; simpl; tauto).
  assert (forall r, A1 r -> A2 r -> False) by (intro; subst A1 A2; simpl; tauto).
  clearbody A1 A2 A.
  
  rewrite sat_sepcon in H1.
  destruct H1 as [s1 [s2 [? [? ?]]]].
  specialize (fun ms_post HH => H s1 ms_post H8 (traces_access_intro tr1 _ _ _ H2 HH)).
  specialize (fun ms_post HH => H0 s2 ms_post H9 (traces_access_intro tr2 _ _ _ H5 HH)).
  clear Tr1 Tr2 H2 H5.
  induction H6.
  + inversion H4; subst; clear H4.
    destruct ms_post; subst; inversion H2.
    subst m A.
    assert (A1 = fun _ => False) by (extensionality r; apply prop_ext; specialize (H3 r); tauto).
    assert (A2 = fun _ => False) by (extensionality r; apply prop_ext; specialize (H3 r); tauto).
    subst A1 A2.
    specialize (H (Terminating s1) (trace_access_nil _)); simpl in H.
    specialize (H0 (Terminating s2) (trace_access_nil _)); simpl in H0.
    rewrite sat_sepcon.
    exists s1, s2.
    split; [| split]; auto.
  + exfalso.
    destruct (res_actions_no_race _ _ H2).
    apply (state_enable_race_actions_spec a1 a2 A1 A2 s1 s2 s_pre); auto.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H10 by auto.
      specialize (H Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H10)).
      inversion H.
    - intro.
      rewrite (thread_local_state_enable_non_resource_action Inv) in H10 by auto.
      specialize (H0 Error (@trace_access_Error _ _ (ThreadLocal_ActionInterpret_resource _ Inv) _ _ _ H10)).
      inversion H0.
  + Abort.
      