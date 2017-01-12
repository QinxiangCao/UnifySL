Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.

Class LocalTraceSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  denote: cmd -> trace state -> Prop;
  denote_defined: forall c s, exists tr, denote c tr /\ begin_state tr s;
  trace_sequential: forall c tr, denote c tr -> sequential_trace tr
}.

Definition access {P: ProgrammingLanguage} {state: Type} {LTS: LocalTraceSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  exists tr, denote c tr /\ begin_end_state s tr ms.

Class SALocalTraceSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {kiM: KripkeIntuitionisticModel state} (LTS: LocalTraceSemantics P state): Type := {
  frame_property: forall c tr' m mf m',
    join m mf m' ->
    denote c tr' ->
    begin_state tr' m' ->
    exists tr,
    denote c tr /\
    begin_state tr m /\
    (end_state tr Error \/
     exists trf,
       sequential_trace trf /\
       begin_state trf mf /\
       (forall k m' n',
         tr' k = Some (m', n') ->
         exists m n mf nf,
         tr k = Some (m, n) /\
         trf k = Some (mf, nf) /\
         lift_Korder nf (Terminating mf) /\
         lift_join n nf n'))
}.

Module ImpLocalTraceSemantics (F: FORWARD) (FT: FORWARD_TRACE with Module F := F).

Export F.
Export FT.

Class ImpLocalTraceSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (LTS: LocalTraceSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  denote_Sskip: forall tr,
    denote Sskip tr -> is_empty_stream tr;
  denote_Ssequence: forall c1 c2 tr,
    denote (Ssequence c1 c2) tr ->
    traces_app (denote c1) (traces_app forward_trace (denote c2)) tr;
  denote_Sifthenelse: forall b c1 c2 tr,
    denote (Sifthenelse b c1 c2) tr ->
    traces_app (forward_trace_with_test (fun s => eval_bool s b)) (denote c1) tr \/
    traces_app (forward_trace_with_test (fun s => ~ eval_bool s b)) (denote c2) tr;
  denote_Swhile: forall b c tr,
    denote (Swhile b c) tr ->
    traces_app (traces_pstar (traces_app (forward_trace_with_test (fun s => eval_bool s b)) (traces_app (denote c) forward_trace))) (forward_trace_with_test (fun s => ~ eval_bool s b)) tr \/
    traces_pomega (traces_app (forward_trace_with_test (fun s => eval_bool s b)) (traces_app (denote c) forward_trace)) tr
}.

End ImpLocalTraceSemantics.

Module Total := ImpLocalTraceSemantics (ProgramState.Total) (Trace.Total).

Module Partial := ImpLocalTraceSemantics (ProgramState.Partial) (Trace.Partial).

Instance Total2Partial_ImpLocalTraceSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} {LTS: LocalTraceSemantics P state} (iLTS: Total.ImpLocalTraceSemantics P state LTS): Partial.ImpLocalTraceSemantics P state LTS.
Proof.
  refine (Partial.Build_ImpLocalTraceSemantics _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _ _).
  + apply Total.denote_Sskip.
  + intros.
    pose proof Total.denote_Ssequence c1 c2 tr H.
    clear H; revert tr H0.
    apply traces_app_mono; [hnf; intros; auto |].
    apply traces_app_mono; [| hnf; intros; auto].
    apply Total2Partial_forward_trace.
  + intros.
    pose proof Total.denote_Sifthenelse b c1 c2 tr H as [ | ].
    - left.
      clear H; revert tr H0.
      apply traces_app_mono; [| hnf; intros; auto].
      apply Total2Partial_forward_trace_with_test.
    - right.
      clear H; revert tr H0.
      apply traces_app_mono; [| hnf; intros; auto].
      apply Total2Partial_forward_trace_with_test.
  + intros.
    pose proof Total.denote_Swhile b c tr H as [ | ].
    - left.
      clear H; revert tr H0.
      apply traces_app_mono.
      * apply traces_pstar_mono.
        apply traces_app_mono; [| apply traces_app_mono].
       ++ apply Total2Partial_forward_trace_with_test.
       ++ hnf; intros; auto.
       ++ apply Total2Partial_forward_trace.
      * apply Total2Partial_forward_trace_with_test.
    - right.
      clear H; revert tr H0.
      apply traces_pomega_mono.
      apply traces_app_mono; [| apply traces_app_mono].
      * apply Total2Partial_forward_trace_with_test.
      * hnf; intros; auto.
      * apply Total2Partial_forward_trace.
Defined.
