Require Import MinimumLogic.Syntax.
Require Import GeneralLogic.Base.
Require Import MinimumLogic.ProofTheory.Minimum.
Require Import PropositionalLogic.Syntax.
Require Import PropositionalLogic.ProofTheory.Intuitionistic.
Require Import PropositionalLogic.ProofTheory.Classical.
Require Import PropositionalLogic.ProofTheory.DeMorgan.
Require Import PropositionalLogic.ProofTheory.GodelDummett.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.
Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_classical_logic
  ; provability_OF_separation_logic
  ; provability_OF_emp_rule
  ].
