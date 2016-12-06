Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.SequentialSemantics.
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
           {rCP: Resource_ConcurrentProgrammingLanguage P}
           {MD: Model}
           {TLBSS: ThreadLocalBigStepSemantics
                     P (model) (resource -> option expr)}
           {SM: Semantics L MD}
           (Inv: resource -> option expr)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  @triple_partial_valid L P MD (guarded_BSS Inv) SM Pre c Post.

Definition guarded_triple_total_valid
           {L: Language}
           {P: ProgrammingLanguage}
           {rCP: Resource_ConcurrentProgrammingLanguage P}
           {MD: Model}
           {TLBSS: ThreadLocalBigStepSemantics
                     P (model) (resource -> option expr)}
           {SM: Semantics L MD}
           (Inv: resource -> option expr)
           (Pre: expr)
           (c: cmd)
           (Post: expr):
  Prop :=
  @triple_total_valid L P MD (guarded_BSS Inv) SM Pre c Post.

(***************************************)
(* Type Classes                        *)
(***************************************)

(*
(* TODO: Resume it *)
Class HoareTriple
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
Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 80, no associativity) : hoare_logic.

Local Open Scope hoare_logic.

Class TripleInterpretation_Partial (L: Language) (P: ProgrammingLanguage) (HLan: Language) {HT: HoareTriple L P HLan} (MD: Model) (BSS: BigStepSemantics P model) (SM: Semantics L MD) (TI: Semantics HLan unit_MD) : Type := {
  partial_valid_spec: forall (P: Assertion) (c: cmd) (Q: Assertion),
    (|== {{ P }} c {{ Q }}) <->
    triple_partial_valid P c Q
}.

Class TripleInterpretation_Total (L: Language) (P: ProgrammingLanguage) (HLan: Language) {HT: HoareTriple L P HLan} (MD: Model) (BSS: BigStepSemantics P model) (SM: Semantics L MD) (TI: Semantics HLan unit_MD) : Type := {
  total_valid_spec: forall (P: Assertion) (c: cmd) (Q: Assertion),
    (|== {{ P }} c {{ Q }}) <->
    triple_total_valid P c Q
}.

*)