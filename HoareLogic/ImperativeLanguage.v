Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Class ImperativeProgrammingLanguage: Type := {
  cmd: Type
}.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Arguments Error {_}.
Arguments NonTerminating {_}.
Arguments Terminating {_} _.

Class BigStepSemantics (Imp: ImperativeProgrammingLanguage) (state: Type): Type := {
  access: state -> cmd -> MetaState state -> Prop
}.

Definition safe {Imp: ImperativeProgrammingLanguage} {state: Type} {BSS: BigStepSemantics Imp state} (s: state) (c: cmd): Prop :=
  ~ access s c Error.

Definition term_norm {Imp: ImperativeProgrammingLanguage} {state: Type} {BSS: BigStepSemantics Imp state} (s: state) (c: cmd): Prop :=
  ~ access s c Error /\ ~ access s c NonTerminating.

Class NormalBigStepSemantics (Imp: ImperativeProgrammingLanguage) (state: Type) (BSS: BigStepSemantics Imp state): Type := {
  access_defined: forall s c, exists ms, access s c ms
}.

Class SABigStepSemantics (Imp: ImperativeProgrammingLanguage) (state: Type) {SA: SeparationAlgebra state} (BSS: BigStepSemantics Imp state): Type := {
  safety_preserve: forall m mf m' c, join m mf m' -> safe m c -> safe m' c;
  terminate_preserve: forall m mf m' c, join m mf m' -> term_norm m c -> term_norm m' c;
  frame_property: forall m mf m' c n', join m mf m' -> safe m c -> access m' c (Terminating n') -> exists n, join n mf n' /\ access m c (Terminating n)
}.

