Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.SequentialSemantics.
Require Import Logic.HoareLogic.HoareLogic_Sequential.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Inductive loop_access_fin
          {state: Type}
          {kiM: KripkeIntuitionisticModel state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> MetaState state -> Prop :=
| loop_access_Terminating:
    forall s1 s2,
      ~ test s1 ->
      Korder s2 s1 ->
      loop_access_fin R test s1 (Terminating s2)
| loop_access_Error:
    forall s1 s2,
      test s1 ->
      Korder s2 s1 ->
      R s2 Error ->
      loop_access_fin R test s1 Error
| loop_access_fin_NonTerminating:
    forall s1 s2,
      test s1 ->
      Korder s2 s1 ->
      R s2 NonTerminating ->
      loop_access_fin R test s1 NonTerminating
| loop_access_step:
    forall s1 s2 s3 s4 ms,
      test s1 ->
      Korder s2 s1 ->
      R s2 (Terminating s3) ->
      Korder s4 s3 ->
      loop_access_fin R test s4 ms ->
      loop_access_fin R test s1 ms.

Inductive loop_access_inf
          {state: Type}
          {kiM: KripkeIntuitionisticModel state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> Prop :=
| loop_access_inf_NonTerminating:
    forall (s1 s2 s3: nat -> state),
      (forall n, test (s1 n)) ->
      (forall n, Korder (s2 n) (s1 n)) ->
      (forall n, R (s2 n) (Terminating (s3 n))) ->
      (forall n, Korder (s1 (S n)) (s3 n)) ->
      loop_access_inf R test (s1 0).

Inductive loop_access
          {state: Type}
          {kiM: KripkeIntuitionisticModel state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> MetaState state -> Prop :=
| loop_access_loop_access_fin:
    forall s ms, loop_access_fin R test s ms ->
      loop_access R test s ms
| loop_access_loop_access_inf:
    forall s, loop_access_inf R test s ->
      loop_access R test s NonTerminating.

Class ImpBigStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (BSS: BigStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  access_Ssequence: forall c1 c2 s ms,
    access s (Ssequence c1 c2) ms ->
    exists ms' ms'',
      access s c1 ms' /\ lift_Korder ms'' ms' /\ lift_access ms'' c2 ms;
  access_Sifthenelse: forall b c1 c2 s ms,
    access s (Sifthenelse b c1 c2) ms ->
    (eval_bool s b /\ exists s', Korder s' s /\ access s' c1 ms) \/
    (~ eval_bool s b /\ exists s', Korder s' s /\ access s' c2 ms);
  access_Swhile: forall b c s ms,
    access s (Swhile b c) ms ->
    loop_access (fun s ms => access s c ms) (fun s => eval_bool s b) s ms
}.

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {iP: ImperativeProgrammingLanguage P}
        {MD: Model}
        {kiM: KripkeIntuitionisticModel model}
        {BSS: BigStepSemantics P model}
        {nBSS: NormalBigStepSemantics P model BSS}
        {iBSS: ImpBigStepSemantics P model BSS}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM}.

Lemma hoare_seq_partial_sound: forall c1 c2 P1 P2 P3,
  triple_partial_valid P1 c1 P2 ->
  triple_partial_valid P2 c2 P3 ->
  triple_partial_valid P1 (Ssequence c1 c2) P3.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Ssequence in H2.
  destruct H2 as [ms' [ms'' [? [? ?]]]].
  specialize (H s ms' H1 H2).
  destruct ms' as [| | s'].
  + inversion H.
  + inversion H3; subst ms''; clear H3.
    inversion H4; auto.
  + inversion H3; subst.
    eapply sat_mono in H; [| exact H7].
    clear H2 H7 H3 s'; rename x into s'.
    apply (H0 s' ms); auto.
    inversion H4; auto.
Qed.

Lemma hoare_seq_total_sound: forall c1 c2 P1 P2 P3,
  triple_total_valid P1 c1 P2 ->
  triple_total_valid P2 c2 P3 ->
  triple_total_valid P1 (Ssequence c1 c2) P3.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Ssequence in H2.
  destruct H2 as [ms' [ms'' [? [? ?]]]].
  specialize (H s ms' H1 H2).
  destruct ms' as [| | s'].
  + inversion H.
  + inversion H.
  + inversion H3; subst.
    eapply sat_mono in H; [| exact H7].
    clear H2 H7 H3 s'; rename x into s'.
    apply (H0 s' ms); auto.
    inversion H4; auto.
Qed.

Lemma hoare_if_partial_sound: forall b c1 c2 B P1 P2,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_partial_valid (P1 && B) c1 P2 ->
  triple_partial_valid (P1 && ~~ B) c2 P2 ->
  triple_partial_valid P1 (Sifthenelse b c1 c2) P2.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Sifthenelse in H3.
  destruct H3; destruct H3 as [? [s' [? ?]]].
  + assert (KRIPKE: s |= P1 && B) by (rewrite sat_andp; firstorder).
    eapply sat_mono in H6; [| eassumption].
    apply (H0 s'); auto.
  + assert (KRIPKE: s |= P1 && ~~ B).
    Focus 1. {
      rewrite sat_andp; split; auto.
      unfold negp; rewrite sat_impp.
      intros.
      rewrite H in H7.
      pose proof eval_bool_stable b _ _ H6.
      simpl in H7, H8.
      rewrite H8 in H7; exfalso; auto.
    } Unfocus.
    eapply sat_mono in H6; [| eassumption].
    apply (H1 s'); auto.
Qed.

Lemma hoare_if_total_sound: forall b c1 c2 B P1 P2,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_total_valid (P1 && B) c1 P2 ->
  triple_total_valid (P1 && ~~ B) c2 P2 ->
  triple_total_valid P1 (Sifthenelse b c1 c2) P2.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Sifthenelse in H3.
  destruct H3; destruct H3 as [? [s' [? ?]]].
  + assert (KRIPKE: s |= P1 && B) by (rewrite sat_andp; firstorder).
    eapply sat_mono in H6; [| eassumption].
    apply (H0 s'); auto.
  + assert (KRIPKE: s |= P1 && ~~ B).
    Focus 1. {
      rewrite sat_andp; split; auto.
      unfold negp; rewrite sat_impp.
      intros.
      rewrite H in H7.
      pose proof eval_bool_stable b _ _ H6.
      simpl in H7, H8.
      tauto.
    } Unfocus.
    eapply sat_mono in H6; [| eassumption].
    apply (H1 s'); auto.
Qed.

Lemma hoare_while_partial_sound: forall b c B P,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_partial_valid (P && B) c P ->
  triple_partial_valid P (Swhile b c) (P && ~~ B).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Swhile in H2.
  inversion H2; subst; clear H2; auto.

  induction H3.
  + eapply sat_mono; [eassumption |].
    rewrite sat_andp.
    split; auto.
    unfold negp.
    rewrite sat_impp; intros.
    rewrite H in H5.
    pose proof eval_bool_stable b _ _ H4.
    simpl in H5, H6.
    tauto.
  + assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
    eapply sat_mono in H5; [| eassumption].
    specialize (H0 _ _ H5 H4).
    apply H0.
  + auto.
  + apply IHloop_access_fin; clear IHloop_access_fin H6.
    assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
    eapply sat_mono in H6; [| eassumption].
    eapply sat_mono; [eassumption |].
    exact (H0 _ _ H6 H4).
Qed.

Lemma hoare_while_total_sound:
  forall {A: Type} (R: A -> A -> Prop) (Wf: well_founded R) (EQ LE: A -> expr) (D: model -> A),
    (forall s v, s |= EQ v <-> D s = v) ->
    (forall s v, s |= LE v <-> R (D s) v) ->
    (forall s1 s2, s1 <= s2 -> D s1 = D s2) ->
    forall b c B P,
     (forall s, s |= B <-> eval_bool s b) ->
     (forall v, triple_total_valid (P && B && EQ v) c (P && LE v)) ->
     triple_total_valid P (Swhile b c) (P && ~~ B).
Proof.
  intros ? ? WF ? ? ? H_EQ H_LE H_D; intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Swhile in H2.
  inversion H2; subst; clear H2; auto.

  Focus 1. {
  induction H3.
  + eapply sat_mono; [eassumption |].
    rewrite sat_andp.
    split; auto.
    unfold negp.
    rewrite sat_impp; intros.
    rewrite H in H5.
    pose proof eval_bool_stable b _ _ H4.
    simpl in H5, H6.
    tauto.
  + assert (KRIPKE: s1 |= P0 && B && EQ (D s2)).
    - rewrite !sat_andp.
      rewrite H_EQ, H, (H_D _ _ H3).
      simpl; tauto.
    - eapply sat_mono in H5; [| eassumption].
      specialize (H0 _ _ _ H5 H4).
      apply H0.
  + assert (KRIPKE: s1 |= P0 && B && EQ (D s2)).
    - rewrite !sat_andp.
      rewrite H_EQ, H, (H_D _ _ H3).
      simpl; tauto.
    - eapply sat_mono in H5; [| eassumption].
      specialize (H0 _ _ _ H5 H4).
      apply H0.
  + apply IHloop_access_fin; clear IHloop_access_fin H6.
    assert (KRIPKE: s1 |= P0 && B && EQ (D s2)).
    - rewrite !sat_andp.
      rewrite H_EQ, H, (H_D _ _ H3).
      simpl; tauto.
    - eapply sat_mono in H6; [| eassumption].
      eapply sat_mono; [eassumption |].
      specialize (H0 _ _ _ H6 H4).
      rewrite sat_andp in H0.
      tauto.
  } Unfocus.
  Focus 1. {
    inversion H3; subst; clear H3.
    specialize (WF (D (s1 0))).
    set (n := 0) in WF, H1; clearbody n.
    remember (D (s1 n)) as D0 eqn:?H.
    revert n H1 H3.
    induction WF.

    intros.
    subst x.
    assert (KRIPKE: s1 n |= P0 && B && EQ (D (s1 n))).
    - rewrite !sat_andp.
      rewrite H_EQ, H.
      specialize (H2 n).
      simpl; tauto.
    - eapply sat_mono in H8; [| apply H4].
      specialize (H0 _ _ _ H8 (H5 _)).
      eapply sat_mono in H0; [| apply H6].
      rewrite sat_andp in H0; destruct H0.
      rewrite H_LE in H9; simpl in H9.
      exact (H3 _ H9 (S n) H0 eq_refl).
  } Unfocus.
Qed.

End soundness.
