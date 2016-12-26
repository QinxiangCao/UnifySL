Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.SigStream.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

Definition trace (state: Type): Type := stream (MetaState state * MetaState state).

Identity Coercion trace_stream: trace >-> stream.

Definition sequential_trace {state: Type} (tr: trace state) : Prop :=
  forall k ms1 ms2 ms3 ms4,
    tr k = Some (ms1, ms2) ->
    tr (S k) = Some (ms3 , ms4) ->
    ms2 = ms3.

Definition begin_state {state: Type} (tr: trace state) (ms: MetaState state): Prop :=
  exists ms', tr 0 = Some (ms, ms').

Definition end_state {state: Type} (tr: trace state) (ms: MetaState state): Prop :=
  (is_inf_stream tr /\ ms = NonTerminating) \/
  (exists n ms', is_n_stream (S n) tr /\ tr n = Some (ms', ms)).

Class SequentialTraceSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  denote: cmd -> trace state -> Prop
}.

Class NormalSequentialTraceSemantics (P: ProgrammingLanguage) (state: Type) (STS: SequentialTraceSemantics P state): Type := {
  trace_non_empty: forall c tr, denote c tr -> tr 0 <> None;
  trace_forward_legal: forall c tr n ms ms', denote c tr -> tr n = Some (ms, ms') -> ms <> NonTerminating /\ ms <> Error
}.

Definition access {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} {STS: SequentialTraceSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  exists tr, denote c tr /\ sequential_trace tr /\ begin_state tr (Terminating s) /\ end_state tr ms.
(*
Class SASequentialTraceSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {kiM: KripkeIntuitionisticModel state} (STS: SequentialTraceSemantics P state): Type := {
  frame_property: forall c tr' m mf m',
    join m mf m' ->
    has_trace c tr' ->
    begin_state tr' (Terminating m') ->
    exists tr (fs: stream state),
    has_trace c tr /\
    begin_state tr (Terminating m) /\
    fs 0 = Some mf /\
    (forall k m mf m' n',
       join m mf m' ->
       tr k = Some (Terminating m) ->
       tr' k = Some (Terminating m') ->
       fs k = Some mf ->
       tr' (S k) = Some n' ->
       exists n nf,
       tr (S k) = Some n /\
       fs (S k) = Some nf /\
       Korder nf mf /\
       lift_join n (Terminating nf) n')
}.

Module ImpSequentialTraceSemantics (D: DECREASE).

Export D.


End ImpBigStepSemantics.

Module Total := ImpBigStepSemantics (ProgramState.Total).

Module Partial := ImpBigStepSemantics (ProgramState.Partial).

Instance Total2Partial_ImpBigStepSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} {BSS: BigStepSemantics P state} (iBSS: Total.ImpBigStepSemantics P state BSS): Partial.ImpBigStepSemantics P state BSS.
Proof.
  refine (Partial.Build_ImpBigStepSemantics _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _).
  + intros.
    pose proof Total.access_Ssequence c1 c2 s ms H
      as [ms' [ms'' [? [? ?]]]].
    exists ms', ms''; split; [| split]; auto.
    apply Total2Partial_decrease; auto.
  + intros.
    pose proof Total.access_Sifthenelse b c1 c2 s ms H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto; exists ms'; split; auto.
      apply Total2Partial_decrease; auto.
    - right; split; auto; exists ms'; split; auto.
      apply Total2Partial_decrease; auto.
  + intros.
    pose proof Total.access_Swhile b c s ms H.
    destruct H0 as [? | [? ?]].
    - left.
      clear H; induction H0.
      * apply Partial.loop_access_Terminating; auto.
        apply Total2Partial_decrease; auto.
      * eapply Partial.loop_access_abnormal; eauto.
        apply Total2Partial_decrease; auto.
      * apply (Partial.loop_access_step _ _ s1 s2 s3 s4); eauto.
    - right; split; auto.
      clear ms H1 H.
      inversion H0; subst.
      econstructor; eauto.
Defined.
*)