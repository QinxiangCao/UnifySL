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
  clos_refl_trans _ lift_step (Terminating (c, s)) (lift_function (pair Sskip) ms) \/
  ms = NonTerminating /\ exists cs: nat -> cmd * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k))).

Class SASmallStepSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state): Type := {
  frame_property: forall (m mf m': cmd * state) n', join (snd m) (snd mf) (snd m') -> step_safe m -> step m' n' -> exists n nf, Korder (snd nf) (snd mf) /\ @lift_join _ (@prod_Join cmd state (equiv_Join cmd) J) n (Terminating nf) n' /\ step m n
}.

Module Partial.

Class ImpSmallStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  step_Ssequence: forall c1 c2 s mcs,
    step (Ssequence c1 c2, s) mcs ->
    mcs = NonTerminating \/
    (exists s', c1 = Sskip /\ Korder s' s /\ mcs = Terminating (c2, s')) \/
    (exists mcs', step (c2, s) mcs' /\ mcs = lift_function (fun cs => (Ssequence c1 (fst cs), snd cs)) mcs');
  step_Sifthenelse: forall b c1 c2 s mcs,
    step (Sifthenelse b c1 c2, s) mcs ->
    mcs = NonTerminating \/
    (eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (c1, s')) \/
    (~ eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (c2, s'));
  step_Swhile: forall b c s mcs,
    step (Swhile b c, s) mcs ->
    mcs = NonTerminating \/
    (eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (Ssequence c (Swhile b c), s')) \/
    (~ eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (Sskip, s'))
}.

End Partial.

Module Total.

Class ImpSmallStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Korder_stable (fun s => eval_bool s b);
  step_Ssequence: forall c1 c2 s mcs,
    step (Ssequence c1 c2, s) mcs ->
    (exists s', c1 = Sskip /\ Korder s' s /\ mcs = Terminating (c2, s')) \/
    (exists mcs', step (c2, s) mcs' /\ mcs = lift_function (fun cs => (Ssequence c1 (fst cs), snd cs)) mcs');
  step_Sifthenelse: forall b c1 c2 s mcs,
    step (Sifthenelse b c1 c2, s) mcs ->
    (eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (c1, s')) \/
    (~ eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (c2, s'));
  step_Swhile: forall b c s mcs,
    step (Swhile b c, s) mcs ->
    (eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (Ssequence c (Swhile b c), s')) \/
    (~ eval_bool s b /\ exists s', Korder s' s /\ mcs = Terminating (Sskip, s'))
}.

End Total.
