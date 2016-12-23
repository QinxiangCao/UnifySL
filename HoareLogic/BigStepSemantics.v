Require Import Coq.Relations.Relation_Operators.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

Class BigStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  access: state -> cmd -> MetaState state -> Prop
}.

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

Class NormalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (BSS: BigStepSemantics P state): Type := {
  access_defined: forall s c, exists ms, access s c ms
}.
