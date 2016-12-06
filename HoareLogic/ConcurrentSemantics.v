Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.SequentialSemantics.

Class ThreadLocalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (guard: Type): Type :=
  guarded_BSS: guard -> BigStepSemantics P state.

Definition tl_access
           {P: ProgrammingLanguage}
           {state: Type}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P state guard}:
  guard -> state -> cmd -> MetaState state -> Prop :=
  fun g => @access _ _ (guarded_BSS g).

(*
Class NormalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (BSS: BigStepSemantics P state): Type := {
  access_defined: forall s c, exists ms, access s c ms
}.
*)