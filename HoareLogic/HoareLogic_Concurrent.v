Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.ConcurrentSemantics.
Require Import Logic.HoareLogic.HoareLogic_Sequential.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Definition guarded_triple_partial_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {MD: Model}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P (model) guard}
           {SM: Semantics L MD}
           (Inv: guard)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  exists h,
  @triple_partial_valid L _ MD (guarded_BSS Inv) SM Pre (existT _ c h) Post.

Definition guarded_triple_total_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {MD: Model}
           {guard: Type}
           {TLBSS: ThreadLocalBigStepSemantics P (model) guard}
           {SM: Semantics L MD}
           (Inv: guard)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  exists h,
  @triple_total_valid L _ MD (guarded_BSS Inv) SM Pre (existT _ c h) Post.

(***************************************)
(* Type Classes                        *)
(***************************************)

Class GuardedHoareTriple
      (L: Language)
      (P: ProgrammingLanguage)
      {rCP: Resource_ConcurrentProgrammingLanguage P}
      (HLan: Language): Type :=
{
  Assertion := @expr L;
  triple: (resource -> option Assertion) ->
          Assertion ->
          cmd ->
          Assertion ->
          @expr HLan
}.

Definition triple_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {rCP: Resource_ConcurrentProgrammingLanguage P}
           {HLan: Language}
           {TI: Semantics HLan unit_MD}
           (t: @expr HLan): Prop :=
  @satisfies _ _ TI tt t.

Notation "|==  x" := (triple_valid x) (at level 71, no associativity) : hoare_logic.
Notation "{{ Inv }} {{ P }} c {{ Q }}" := (triple Inv P c Q) (at level 80, no associativity) : guarded_hoare_logic.


