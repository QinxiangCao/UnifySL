Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.

Class SimpleSmallStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  simple_step: cmd * state -> cmd * state -> Prop
}.

Definition step {P: ProgrammingLanguage} {state: Type} {SSSS: SimpleSmallStepSemantics P state} (cs: cmd * state) (mcs: MetaState (cmd * state)) :=
  match mcs with
  | Terminating cs0 => simple_step cs cs0
  | NonTerminating => False
  | Error => forall cs0, ~ simple_step cs cs0
  end.
