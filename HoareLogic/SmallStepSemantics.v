Require Import Coq.Relations.Relation_Operators.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
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

Class NormalSmallStepSemantics (P: ProgrammingLanguage) (state: Type) (SSS: SmallStepSemantics P state): Type := {
  step_defined: forall cs, exists mcs, step cs mcs
}.

Definition access {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} {SSS: SmallStepSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  
    match ms with
    | Terminating s0 => clos_refl_trans _ lift_step (Terminating (c, s))  (Terminating (Sskip, s0))
    | NonTerminating => clos_refl_trans _ lift_step (Terminating (c, s)) NonTerminating \/ exists cs: nat -> cmd * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k)))
    | Error => clos_refl_trans _ lift_step (Terminating (c, s)) Error
    end.

