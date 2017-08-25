Require Import Coq.Relations.Relation_Operators.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class Action (action: Type): Type := {
  trace := list action;
  traces := trace -> Prop
}.

Definition singleton_trace {action: Type} {Ac: Action action} (a: action): trace := cons a nil.

Definition singleton_traces {action: Type} {Ac: Action action} (tr: trace): traces := eq tr.

Definition trace_app {action: Type} {Ac: Action action}: trace -> trace -> trace := @app _.

Inductive traces_app {action: Type} {Ac: Action action}: traces -> traces -> traces :=
  traces_app_intro: forall tr1 tr2 (Tr1 Tr2: traces), Tr1 tr1 -> Tr2 tr2 -> traces_app Tr1 Tr2 (trace_app tr1 tr2).

Class Command2Traces (P: ProgrammingLanguage) (action: Type) {Ac: Action action}: Type := {
  cmd_denote: cmd -> traces
}.

Class ActionInterpret (state: Type) (action: Type) {Ac: Action action}: Type := {
  state_enable: action -> state -> MetaState state -> Prop (*;
  state_enable_pf: forall a s ms1 ms2, state_enable a s ms1 -> state_enable a s ms2 -> ms1 = ms2*)
}.

Class TraceSemantics (P: ProgrammingLanguage) (state: Type) (action: Type) {Ac: Action action}: Type := {
  c2t :> Command2Traces P action;
  ac_sen :> ActionInterpret state action
}.

Class Action_Resource (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action}: Type := {
  Aacquire_res: resource -> action;
  Arelease_res: resource -> action;
}.

Definition is_resource_action {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (a: action) := exists r, a = Aacquire_res r \/ a = Arelease_res r.

Inductive res_enable {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource}: action -> resources -> resources -> Prop :=
| res_enable_acq: forall r A1 A2, (forall r0, A1 r0 \/ r = r0 <-> A2 r0) -> ~ A1 r -> res_enable (Aacquire_res r) A1 A2
| res_enable_rel: forall r A1 A2, (forall r0, A2 r0 \/ r = r0 <-> A1 r0) -> ~ A2 r -> res_enable (Arelease_res r) A1 A2
| res_enable_other: forall a A, ~ is_resource_action a -> res_enable a A A.

Class Action_Parallel (action: Type) {Ac: Action action}: Type := {
  race: action;
  race_actions: action -> action -> Prop;
}.

Class NormalAction_Parallel_Resource (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcP: Action_Parallel action} {AcR: Action_Resource action resource}: Type := {
  res_actions_no_race: forall a1 a2, race_actions a1 a2 -> ~ is_resource_action a1 /\ ~ is_resource_action a2
}.

Inductive trace_interleave {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcP: Action_Parallel action} {AcR: Action_Resource action resource}: resources -> resources -> trace -> trace -> trace -> Prop :=
| trace_interleave_nil_nil: forall (A1 A2: resources), trace_interleave A1 A2 nil nil nil
| trace_interleave_race: forall (A1 A2: resources) a1 tr1 a2 tr2, race_actions a1 a2 -> trace_interleave A1 A2 (cons a1 tr1) (cons a2 tr2) (cons race nil)
| trace_interleave_left: forall (A1 A1' A2: resources) a1 tr1 tr2 tr, res_enable a1 A1 A1' -> trace_interleave A1' A2 tr1 tr2 tr -> trace_interleave A1 A2 (cons a1 tr1) tr2 (cons a1 tr)
| trace_interleave_right: forall (A1 A2 A2': resources) tr1 a2 tr2 tr, res_enable a2 A2 A2' -> trace_interleave A1 A2' tr1 tr2 tr -> trace_interleave A1 A2 tr1 (cons a2 tr2) (cons a2 tr).

Inductive traces_interleave {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcP: Action_Parallel action} {AcR: Action_Resource action resource}: traces -> traces -> traces :=
| traces_interleave_intro: forall A1 A2 (Tr1 Tr2: traces) tr1 tr2 tr, Tr1 tr1 -> Tr2 tr2 -> trace_interleave A1 A2 tr1 tr2 tr -> traces_interleave Tr1 Tr2 tr.

Class ActionInterpret_resource (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (ac_sem: ActionInterpret (state * resources) action): Type := {
  state_enable_resource_action: forall a (A1 A2: resources) (s: state),
    is_resource_action a -> res_enable a A1 A2 -> state_enable a (s, A1) (Terminating (s, A2));
  state_enable_non_resource_action: forall a (A1 A2: resources) (s1 s2: state),
    ~ is_resource_action a -> state_enable a (s1, A1) (Terminating (s2, A2)) -> A1 = A2
}.

Class Command2Traces_Sresource (P: ProgrammingLanguage) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} {CPR: ConcurrentProgrammingLanguage_Sresource P resource} (c2t: Command2Traces P action): Type := {
  Sresource_denote: forall r c, cmd_denote (Sresource r c) = traces_app (singleton_traces (singleton_trace (Aacquire_res r))) (traces_app (cmd_denote c) (singleton_traces (singleton_trace (Arelease_res r))))
}.

Class Command2Traces_Sparallel_resource (P: ProgrammingLanguage) (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcP: Action_Parallel action} {AcR: Action_Resource action resource} {CPP: ConcurrentProgrammingLanguage_Sparallel P} (c2t: Command2Traces P action): Type := {
  Sparallel_denote: forall c1 c2, cmd_denote (Sparallel c1 c2) = traces_interleave (cmd_denote c1) (cmd_denote c2)
}.

Class SAActionInterpret_resource (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (ac_sem: ActionInterpret (state * resources) action) {J: Join state} {state_R: Relation state}: Type := {
  frame_property_Terminating: forall (a: action) (A1 A2: resources) (m1 f n1 n2: state),
    @join _ J m1 f n1 ->
    ~ state_enable a (m1, A1) Error ->
    state_enable a (n1, A1) (Terminating (n2, A2)) ->
    exists m2, @join _ J m2 f n2 /\ state_enable a (m1, A1) (Terminating (n2, A2));
  frame_property_NonTerminating: forall (a: action) (A1: resources) (m1 f n1: state),
    @join _ J m1 f n1 ->
    ~ state_enable a (m1, A1) Error ->
    state_enable a (n1, A1) NonTerminating ->
    state_enable a (m1, A1) NonTerminating;
  frame_property_Error: forall (a: action) (A1: resources) (m1 f n1: state),
    @join _ J m1 f n1 ->
    state_enable a (n1, A1) Error ->
    state_enable a (m1, A1) Error
}.

Inductive trace_access {state: Type} {action: Type} {Ac: Action action} {ac_sem: ActionInterpret state action}: trace -> state -> MetaState state -> Prop :=
| trace_access_nil: forall s, trace_access nil s (Terminating s)
| trace_access_NonTerminating: forall a tr s, state_enable a s NonTerminating -> trace_access (cons a tr) s NonTerminating
| trace_access_Error: forall a tr s, state_enable a s Error -> trace_access (cons a tr) s Error
| trace_access_Terminating: forall a tr s s' ms, state_enable a s (Terminating s') -> trace_access tr s' ms -> trace_access (cons a tr) s ms.

Inductive traces_access {state: Type} {action: Type} {Ac: Action action} {ac_sem: ActionInterpret state action}: traces -> state -> MetaState state -> Prop :=
| traces_access_intro: forall tr (Tr: traces) s ms, Tr tr -> trace_access tr s ms -> traces_access Tr s ms.

Definition greatest {A: Type} {R: Relation A} (s: A -> Prop) (a: A): Prop :=
  forall a0, s a0 -> a0 <= a.

Inductive thread_local_state_enable {state: Type} {J: Join state} {state_R: Relation state} {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} {ac_sem: ActionInterpret (state * resources) action} (Inv: resource * (state -> Prop) -> Prop) : action -> state * resources -> MetaState (state * resources) -> Prop :=
| thread_local_state_enable_acq: forall r A1 A2 I m f n,
    (forall r0, A1 r0 \/ r = r0 <-> A2 r0) -> ~ A1 r ->
    Inv (r, I) -> I f ->
    join m f n ->
    thread_local_state_enable Inv (Aacquire_res r) (m, A1) (Terminating (n, A2))
| thread_local_state_enable_rel_succ: forall r A1 A2 I m n,
    (forall r0, A2 r0 \/ r = r0 <-> A1 r0) -> ~ A2 r ->
    Inv (r, I) ->
    greatest (fun n => exists f, I f /\ join n f m) n ->
    thread_local_state_enable Inv (Arelease_res r) (m, A1) (Terminating (n, A2))
| thread_local_state_enable_rel_fail: forall r A1 A2 I m,
    (forall r0, A2 r0 \/ r = r0 <-> A1 r0) -> ~ A2 r ->
    Inv (r, I) ->
    (forall n, ~ exists f, I f /\ join n f m) ->
    thread_local_state_enable Inv (Arelease_res r) (m, A1) Error
| thread_local_state_enable_non_resource: forall a s s',
    ~ is_resource_action a ->
    state_enable a s s' ->
    thread_local_state_enable Inv a s s'.

Definition ThreadLocal_ActionInterpret_resource {state: Type} {J: Join state} {state_R: Relation state} {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (ac_sem: ActionInterpret (state * resources) action) (Inv: resource * (state -> Prop) -> Prop): ActionInterpret (state * resources) action :=
  Build_ActionInterpret _ _ _ (thread_local_state_enable Inv).

Definition ThreadLocal_BBS (P: ProgrammingLanguage) {state: Type} {J: Join state} {state_R: Relation state} {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (TS: TraceSemantics P (state * resources) action) (Inv: resource * (state -> Prop) -> Prop): BigStepSemantics P state.
Abort.

