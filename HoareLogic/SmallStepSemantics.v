Require Import Coq.Relations.Relation_Operators.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.SeparationAlgebraExamples.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

Class SmallStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  step: cmd * state -> MetaState (cmd * state) -> Prop
}.

Definition lift_step
          {P: ProgrammingLanguage}
          {state: Type}
          {SSS: SmallStepSemantics P state}
          (mcs1: MetaState (cmd * state))
          (mcs2: MetaState (cmd * state)): Prop :=
  lift_relation (fun cs => step cs) mcs1 mcs2.

Definition step_safe
           {P: ProgrammingLanguage}
           {state: Type}
           {SSS: SmallStepSemantics P state}
           (cs: cmd * state):
  Prop :=
  ~ step cs Error.

Definition step_term_norm
           {P: ProgrammingLanguage}
           {state: Type}
           {SSS: SmallStepSemantics P state}
           (cs: cmd * state):
  Prop :=
  ~ step cs Error /\ ~ step cs NonTerminating.

Class NormalSmallStepSemantics (P: ProgrammingLanguage) (state: Type) (SSS: SmallStepSemantics P state): Type := {
  step_defined: forall cs, exists mcs, step cs mcs
}.

Definition access {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} {SSS: SmallStepSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  
    match ms with
    | Terminating s0 => clos_refl_trans _ lift_step (Terminating (c, s))  (Terminating (Sskip, s0))
    | NonTerminating => clos_refl_trans _ lift_step (Terminating (c, s)) NonTerminating \/ exists cs: nat -> cmd * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k)))
    | Error => clos_refl_trans _ lift_step (Terminating (c, s)) Error
    end.

Class SASmallStepSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state): Type := {
  frame_property: forall (m mf m': cmd * state) n', join (snd m) (snd mf) (snd m') -> step_safe m -> step m' n' -> exists n nf, Korder (snd nf) (snd mf) /\ @lift_join _ (@prod_Join cmd state (equiv_Join cmd) J) n (Terminating nf) n' /\ step m n
}.

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
(*
Class ImpSmallStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  step_Ssequence: forall c1 c2 s mcs,
    step (Ssequence c1 c2, s) mcs ->
    (exists s', c1 = Sskip /\ Korder s' s /\ mcs = Terminating (c2, s')) \/
    (exists mcs', step (c2, s) mcs' /\ mcs = lift_function (fun cs => (Ssequence c1 (fst cs), snd cs)) mcs')
}.
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

*)