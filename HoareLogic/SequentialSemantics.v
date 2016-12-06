Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Arguments Error {_}.
Arguments NonTerminating {_}.
Arguments Terminating {_} _.

Inductive lift_Korder
          {state: Type}
          {ki_state: KripkeIntuitionisticModel state}:
  MetaState state -> MetaState state -> Prop :=
| lift_Korder_Error:
    lift_Korder Error Error
| lift_Korder_NonTerminating:
    lift_Korder NonTerminating NonTerminating
| lift_Korder_Terminating:
    forall x y, Korder x y -> lift_Korder (Terminating x) (Terminating y).

Inductive lift_join
          {state: Type}
          {J_state: Join state}:
  MetaState state -> MetaState state -> MetaState state -> Prop :=
| lift_join_Error1:
    forall mx my, lift_join Error mx my
| lift_join_Error2:
    forall mx my, lift_join mx Error my
| lift_join_NonTerminating1:
    forall x, lift_join NonTerminating (Terminating x) NonTerminating
| lift_join_NonTerminating2:
    forall x, lift_join (Terminating x) NonTerminating NonTerminating
| lift_join_NonTerminating3:
    lift_join NonTerminating NonTerminating NonTerminating
| lift_join_Terminating:
    forall x y z,
      join x y z ->
      lift_join (Terminating x) (Terminating y) (Terminating z).

(*
Instance MetaState_SA (state: Type) {SA: SeparationAlgebra state}: SeparationAlgebra (MetaState state).
*)

Class BigStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  access: state -> cmd -> MetaState state -> Prop
}.

Inductive lift_access
          {P: ProgrammingLanguage}
          {state: Type}
          {BSS: BigStepSemantics P state}:
  MetaState state -> cmd -> MetaState state -> Prop :=
| lift_access_Error:
    forall c, lift_access Error c Error
| lift_access_NonTerminating:
    forall c, lift_access NonTerminating c NonTerminating
| lift_access_Terminating:
    forall s c ms, access s c ms -> lift_access (Terminating s) c ms.

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

