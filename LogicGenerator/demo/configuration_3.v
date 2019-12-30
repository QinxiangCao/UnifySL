Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [primitive_judgement derivable
  ;FROM_derivable_TO_provable
  ].

Definition transparent_names: list parameter :=
  [].

Definition primitive_rule_classes :=
  [ derivitive_OF_basic_setting
  ; derivitive_OF_impp
  ; derivitive_OF_propositional_connectives
  ; GEN_provable_FROM_derivable
  ].
