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
    forall s, ~ test s -> loop_access_fin R test s (Terminating s)
| loop_access_Error:
    forall s1 s2,
      test s1 ->
      Korder s1 s2 ->
      R s2 Error ->
      loop_access_fin R test s1 Error
| loop_access_fin_NonTerminating:
    forall s1 s2,
      test s1 ->
      Korder s1 s2 ->
      R s2 NonTerminating ->
      loop_access_fin R test s1 NonTerminating
| loop_access_step:
    forall s1 s2 s3 s4 ms,
      test s1 ->
      Korder s1 s2 ->
      R s2 (Terminating s3) ->
      Korder s3 s4 ->
      loop_access_fin R test s3 ms ->
      loop_access_fin R test s1 ms.

Inductive loop_access_inf
          {state: Type}
          {kiM: KripkeIntuitionisticModel state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> Prop :=
| loop_access_inf_NonTerminating:
    forall (s1 s2 s3: nat -> state),
      (forall n, test (s1 n)) ->
      (forall n, Korder (s1 n) (s2 n)) ->
      (forall n, R (s2 n) (Terminating (s3 n))) ->
      (forall n, Korder (s3 n) (s1 (S n))) ->
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
  access_Ssequence: forall c1 c2 s ms,
    access s (Ssequence c1 c2) ms ->
    exists ms' ms'',
      access s c1 ms' /\ lift_Korder ms'' ms' /\ lift_access ms'' c2 ms;
  access_Sifthenelse_true: forall b c1 c2 s ms,
    access s (Sifthenelse b c1 c2) ms ->
    eval_bool s b ->
    exists s', Korder s s' /\ access s' c1 ms;
  access_Sifthenelse_false: forall b c1 c2 s ms,
    access s (Sifthenelse b c1 c2) ms ->
    ~ eval_bool s b ->
    exists s', Korder s s' /\ access s' c2 ms;
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

End soundness.
