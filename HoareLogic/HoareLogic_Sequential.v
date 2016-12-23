Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Definition triple_partial_valid {L: Language} {P: ProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics P (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => True
  | Terminating s_post => KRIPKE: s_post |= Post
  end.

Definition triple_total_valid {L: Language} {P: ProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics P (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => False
  | Terminating s_post => KRIPKE: s_post |= Post
  end.

(***************************************)
(* Type Classes                        *)
(***************************************)

Class HoareTriple (L: Language) (P: ProgrammingLanguage) (HLan: Language): Type := {
  Assertion := @expr L;
  triple: Assertion -> cmd -> Assertion -> @expr HLan
}.

Definition triple_valid {L: Language} {P: ProgrammingLanguage} {HLan: Language} {TI: Semantics HLan unit_MD} (t: @expr HLan): Prop := @satisfies _ _ TI tt t.

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
