Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.

(* Change the name to local/global trace semantics. *)
Class SequentialTraceSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  denote: cmd -> trace state -> Prop;
  trace_non_empty: forall c tr, denote c tr -> tr 0 <> None;
  trace_forward_legal: forall c tr n ms ms', denote c tr -> tr n = Some (ms, ms') -> ms <> NonTerminating /\ ms <> Error;
  trace_sequential: forall c tr, denote c tr -> sequential_trace tr
}.

Definition access {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} {STS: SequentialTraceSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  exists tr, denote c tr /\ begin_state tr (Terminating s) /\ end_state tr ms.

Class SASequentialTraceSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {kiM: KripkeIntuitionisticModel state} (STS: SequentialTraceSemantics P state): Type := {
  frame_property: forall c tr' m mf m',
    join m mf m' ->
    denote c tr' ->
    begin_state tr' (Terminating m') ->
    exists tr,
    denote c tr /\
    begin_state tr (Terminating m) /\
    (end_state tr Error \/
     exists trf,
       sequential_trace trf /\
       begin_state trf (Terminating mf) /\
       (forall k m' n',
         tr' k = Some (m', n') ->
         exists m n mf nf,
         tr k = Some (m, n) /\
         trf k = Some (mf, nf) /\
         lift_Korder nf mf /\
         lift_join n nf n'))
}.

Module ImpLocalTraceSemantics (D: DECREASE) (DT: DECREASE_TRACE with Module D := D).

Export D.
Export DT.

Class ImpLocalTraceSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (STS: SequentialTraceSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  denote_Ssequence: forall c1 c2 tr,
    denote (Ssequence c1 c2) tr ->
    traces_app (denote c1) (traces_app decrease_trace (denote c2)) tr;
  denote_Sifthenelse: forall b c1 c2 tr,
    denote (Sifthenelse b c1 c2) tr ->
    traces_app (decrease_trace_with_test (fun s => eval_bool s b)) (denote c1) tr \/
    traces_app (decrease_trace_with_test (fun s => ~ eval_bool s b)) (denote c2) tr;
  denote_Swhile: forall b c tr,
    denote (Swhile b c) tr ->
    traces_app (traces_pstar (traces_app (decrease_trace_with_test (fun s => eval_bool s b)) (denote c))) (decrease_trace_with_test (fun s => ~ eval_bool s b)) tr \/
    traces_pomega (traces_app (decrease_trace_with_test (fun s => eval_bool s b)) (denote c)) tr
}.

End ImpLocalTraceSemantics.

Module Total := ImpLocalTraceSemantics (ProgramState.Total) (Trace.Total).

Module Partial := ImpLocalTraceSemantics (ProgramState.Partial) (Trace.Partial).

(*
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