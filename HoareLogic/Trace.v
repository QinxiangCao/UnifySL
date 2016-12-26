Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.PropositionalLogic.KripkeSemantics.
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

Definition traces_app {state: Type} (d1 d2: trace state -> Prop): trace state -> Prop :=
  fun tr =>
    (exists tr1 tr2, d1 tr1 /\ d2 tr2 /\ tr = stream_app tr1 tr2) \/
    (exists tr1, d1 tr1 /\ (end_state tr1 NonTerminating \/ end_state tr1 Error) /\ tr = tr1).

Fixpoint traces_power {state: Type} (d: trace state -> Prop) (n: nat): trace state -> Prop :=
  match n with
  | 0 => is_empty_stream
  | S n => traces_app (traces_power d n) d
  end.

Definition traces_pstar {state: Type} (d: trace state -> Prop): trace state -> Prop :=
  fun tr => exists n, traces_power d n tr.

Definition traces_pomega {state: Type} (d: trace state -> Prop): trace state -> Prop :=
  fun tr => exists f, tr = stream_capp f /\ forall n, d (f n).

Module Type DECREASE_TRACE.

Declare Module D: DECREASE.

Parameter decrease_trace: forall {state: Type} {kiM: KripkeIntuitionisticModel state}, trace state -> Prop.

Parameter decrease_trace_with_test: forall {state: Type} {kiM: KripkeIntuitionisticModel state} (P: state -> Prop), trace state -> Prop.

End DECREASE_TRACE.

Module DecreaseTrace (D: DECREASE) <: DECREASE_TRACE with Module D := D.

Module D := D.
Export D.

Definition decrease_trace {state: Type} {kiM: KripkeIntuitionisticModel state}: trace state -> Prop :=
  fun tr => is_fin_stream tr /\ forall n ms ms', tr n = Some (ms, ms') -> decrease ms ms'.

Definition decrease_trace_with_test {state: Type} {kiM: KripkeIntuitionisticModel state} (P: state -> Prop) : trace state -> Prop :=
  fun tr => decrease_trace tr /\ exists ms, begin_state tr ms /\
    match ms with
    | Terminating s => P s
    | _ => False
    end.

End DecreaseTrace.

Module Partial := DecreaseTrace (ProgramState.Partial).
Module Total := DecreaseTrace (ProgramState.Total).
