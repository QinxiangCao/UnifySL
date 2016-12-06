Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Arguments Error {_}.
Arguments NonTerminating {_}.
Arguments Terminating {_} _.

Class BigStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  access: state -> cmd -> MetaState state -> Prop
}.

Definition safe {P: ProgrammingLanguage} {state: Type} {BSS: BigStepSemantics P state} (s: state) (c: cmd): Prop :=
  ~ access s c Error.

Definition term_norm {P: ProgrammingLanguage} {state: Type} {BSS: BigStepSemantics P state} (s: state) (c: cmd): Prop :=
  ~ access s c Error /\ ~ access s c NonTerminating.

Class NormalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (BSS: BigStepSemantics P state): Type := {
  access_defined: forall s c, exists ms, access s c ms
}.

