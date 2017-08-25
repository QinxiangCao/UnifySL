Require Import Coq.Relations.Relation_Operators.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

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

Class TraceSemantics (P: ProgrammingLanguage) (state: Type) (action: Type) {Ac: Action action}: Type := {
  cmd_denote: cmd -> traces;
  state_enable: action -> state -> MetaState state -> Prop;
  state_enable_pf: forall a s ms1 ms2, state_enable a s ms1 -> state_enable a s ms2 -> ms1 = ms2
}.

Class Action_Resource (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action}: Type := {
  Aacquire_res: resource -> action;
  Arelease_res: resource -> action;
}.

Definition is_resource_action {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} (a: action) := exists r, a = Aacquire_res r \/ a = Arelease_res r.

Inductive res_enable {action: Type} {resource: Type} {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource}: action -> resources -> resources -> Prop :=
| res_enable_acq: forall r A1 A2, (forall r0, A1 r0 \/ r = r0 <-> A2 r0) -> res_enable (Aacquire_res r) A1 A2
| res_enable_rel: forall r A1 A2, (forall r0, A1 r0 /\ r <> r0 <-> A2 r0) -> res_enable (Arelease_res r) A1 A2
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

Class TraceSemantics_resource (P: ProgrammingLanguage) (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} {Tr: TraceSemantics P (state * resources) action}: Type := {
  state_enable_resource_action: forall a (A1 A2: resources) (s: state),
    is_resource_action a -> res_enable a A1 A2 -> state_enable a (s, A1) (Terminating (s, A2))
}.

Class TraceSemantics_Sresource (P: ProgrammingLanguage) (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcR: Action_Resource action resource} {CPR: ConcurrentProgrammingLanguage_Sresource P resource} {Tr: TraceSemantics P (state * resources) action}: Type := {
  Sresource_denote: forall r c, cmd_denote (Sresource r c) = traces_app (singleton_traces (singleton_trace (Aacquire_res r))) (traces_app (cmd_denote c) (singleton_traces (singleton_trace (Arelease_res r))))
}.

Class TraceSemantics_Sparallel_resource (P: ProgrammingLanguage) (state: Type) (action: Type) (resource: Type) {Res: Resource resource} {Ac: Action action} {AcP: Action_Parallel action} {AcR: Action_Resource action resource} {CPP: ConcurrentProgrammingLanguage_Sparallel P} {Tr: TraceSemantics P (state * resources) action}: Type := {
  Sparallel_denote: forall c1 c2, cmd_denote (Sparallel c1 c2) = traces_interleave (cmd_denote c1) (cmd_denote c2)
}.

(*
Definition lift_access
          {P: ProgrammingLanguage}
          {state: Type}
          {BSS: BigStepSemantics P state}
          (ms1: MetaState state)
          (c: cmd)
          (ms2: MetaState state): Prop :=
  lift_relation (fun s => access s c) ms1 ms2.

Definition safe
           {P: ProgrammingLanguage}
           {state: Type}
           {BSS: BigStepSemantics P state}
           (s: state)
           (c: cmd):
  Prop :=
  ~ access s c Error.

Definition term_norm
           {P: ProgrammingLanguage}
           {state: Type}
           {BSS: BigStepSemantics P state}
           (s: state)
           (c: cmd):
  Prop :=
  ~ access s c Error /\ ~ access s c NonTerminating.

Class SABigStepSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {state_R: Relation state} (BSS: BigStepSemantics P state): Type := {
  frame_property: forall m mf m' c n', join m mf m' -> access m' c n' -> exists n nf, mf <= nf /\ lift_join n (Terminating nf) n' /\ access m c n
}.

Module ImpBigStepSemantics (F: FORWARD).

Export F.

Inductive loop_access_fin
          {state: Type}
          {state_R: Relation state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> MetaState state -> Prop :=
| loop_access_Terminating:
    forall s1 ms2,
      ~ test s1 ->
      forward (Terminating s1) ms2 ->
      loop_access_fin R test s1 ms2
| loop_access_abnormal:
    forall s1 ms2 ms3,
      test s1 ->
      forward (Terminating s1) ms2 ->
      lift_relation R ms2 ms3 ->
      ms3 = Error \/ ms3 = NonTerminating ->
      loop_access_fin R test s1 ms3
| loop_access_step:
    forall s1 s2 s3 s4 ms,
      test s1 ->
      s1 <= s2 ->
      R s2 (Terminating s3) ->
      s3 <= s4 ->
      loop_access_fin R test s4 ms ->
      loop_access_fin R test s1 ms.

Inductive loop_access_inf
          {state: Type}
          {state_R: Relation state}
          (R: state -> MetaState state -> Prop)
          (test: state -> Prop): state -> Prop :=
| loop_access_inf_NonTerminating:
    forall (s1 s2 s3: nat -> state),
      (forall n, test (s1 n)) ->
      (forall n, s1 n <= s2 n) ->
      (forall n, R (s2 n) (Terminating (s3 n))) ->
      (forall n, s3 n <= s1 (S n)) ->
      loop_access_inf R test (s1 0).

Class ImpBigStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} (BSS: BigStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Krelation_stable_Kdenote (fun s => eval_bool s b);
  access_Ssequence: forall c1 c2 s ms,
    access s (Ssequence c1 c2) ms ->
    exists ms' ms'',
      access s c1 ms' /\ forward ms' ms'' /\ lift_access ms'' c2 ms;
  access_Sifthenelse: forall b c1 c2 s ms,
    access s (Sifthenelse b c1 c2) ms ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ lift_access ms' c1 ms) \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ lift_access ms' c2 ms);
  access_Swhile: forall b c s ms,
    access s (Swhile b c) ms ->
    (loop_access_fin (fun s ms => access s c ms) (fun s => eval_bool s b) s ms) \/
    (loop_access_inf (fun s ms => access s c ms) (fun s => eval_bool s b) s /\ ms = NonTerminating)
}.

End ImpBigStepSemantics.

Module Total := ImpBigStepSemantics (ProgramState.Total).

Module Partial := ImpBigStepSemantics (ProgramState.Partial).

Instance Total2Partial_ImpBigStepSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} {BSS: BigStepSemantics P state} (iBSS: Total.ImpBigStepSemantics P state BSS): Partial.ImpBigStepSemantics P state BSS.
Proof.
  refine (Partial.Build_ImpBigStepSemantics _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _).
  + intros.
    pose proof Total.access_Ssequence c1 c2 s ms H
      as [ms' [ms'' [? [? ?]]]].
    exists ms', ms''; split; [| split]; auto.
    apply Total2Partial_forward; auto.
  + intros.
    pose proof Total.access_Sifthenelse b c1 c2 s ms H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto; exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto; exists ms'; split; auto.
      apply Total2Partial_forward; auto.
  + intros.
    pose proof Total.access_Swhile b c s ms H.
    destruct H0 as [? | [? ?]].
    - left.
      clear H; induction H0.
      * apply Partial.loop_access_Terminating; auto.
        apply Total2Partial_forward; auto.
      * eapply Partial.loop_access_abnormal; eauto.
        apply Total2Partial_forward; auto.
      * apply (Partial.loop_access_step _ _ s1 s2 s3 s4); eauto.
    - right; split; auto.
      clear ms H1 H.
      inversion H0; subst.
      econstructor; eauto.
Defined.
*)