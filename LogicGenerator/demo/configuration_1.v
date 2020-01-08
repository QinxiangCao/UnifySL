Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ;FROM_sepcon_TO_iter_sepcon
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
  ; provability_OF_sepcon_rule_AS_weak_iffp
  ; provability_OF_sepcon_rule_AS_mono
  ; provability_OF_sepcon_orp_rule
  ; provability_OF_sepcon_falsep_rule
  ; provability_OF_emp_rule_AS_iffp
  ].
