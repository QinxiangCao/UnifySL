Require Import LogicGenerator.Utils.
Require Import MinimunLogic.Syntax.
Require Import GeneralLogic.Base.
Require Import MinimunLogic.ProofTheory.Minimun.
Require Import PropositionalLogic.Syntax.
Require PropositionalLogic.ProofTheory.Intuitionistic.
Require PropositionalLogic.ProofTheory.Classical.

Definition minimum := true.
Definition propositional_intuitionistic := true.
Definition propositional_classical := true.
Definition propositional_demorgan := true.
Definition propositional_godeldummett := true.

Import NameListNotations.

Section Transparent.
  Context {L : Base.Language}
          {minL : MinimunLanguage L}
          {pL : PropositionalLanguage L}.
  Definition transparent_defs :=
    [ expr
    ; andp
    ].
End Transparent.

Module Minimum.
  Section Syntax.
    Context {L : Base.Language}
            {minL : MinimunLanguage L}.
    Definition connectives := [ impp ].
  End Syntax.

  Section ProofTheory.
    Context {L : Language}
            {minL : MinimunLanguage L}
            {Gamma : ProofTheory L}
            {minAx : MinimunAxiomatization L Gamma}.
    Definition basic_rules :=
      [ modus_ponens
      ; axiom1
      ; axiom2
      ].
    Definition derived_rules :=
      [ provable_impp_refl
      ; provable_impp_arg_switch
      ; provable_impp_trans
      ].
    Definition multi_imp_derived_rules :=
      [ provable_multi_imp_shrink
      ; provable_multi_imp_arg_switch1
      ; provable_multi_imp_arg_switch2
      ; provable_add_multi_imp_left_head
      ; provable_add_multi_imp_left_tail
      ; provable_multi_imp_modus_ponens
      ; provable_multi_imp_weaken
      ].
  End ProofTheory.
End Minimum.

Module Propositional.
  Section Syntax.
    Context {L : Language}
            {pL : PropositionalLanguage L}.
    Definition connectives :=
      [ andp
      ; orp
      ; falsep
      ].
  End Syntax.

  Section ProofTheory.
    Import PropositionalLogic.ProofTheory.Intuitionistic.
    Import PropositionalLogic.ProofTheory.Classical.
    Import PropositionalLogic.ProofTheory.DeMorgan.
    Import PropositionalLogic.ProofTheory.GodelDummett.
    Context {L : Language}
            {minL : MinimunLanguage L}
            {pL : PropositionalLanguage L}
            {Gamma : ProofTheory L}
            {minAx : MinimunAxiomatization L Gamma}
            {ipGamma: IntuitionisticPropositionalLogic L Gamma}
            {cpGamma: ClassicalPropositionalLogic L Gamma}
            {dmpGamma: DeMorganPropositionalLogic L Gamma}
            {gdpGamma: GodelDummettPropositionalLogic L Gamma}.

    Definition intuitionistic_basic_rules :=
      [ andp_intros
      ; andp_elim1
      ; andp_elim2
      ; orp_intros1
      ; orp_intros2
      ; orp_elim
      ; falsep_elim
      ].
    Definition intuitionistic_derived_rules :=
      [ demorgan_orp_negp
      ; demorgan_negp_orp
      ; provable_truep
      ; andp_comm
      ; andp_assoc
      ; orp_comm
      ; orp_assoc
      ; andp_dup
      ; orp_dup
      ; impp_curry
      ; impp_uncurry
      ].
    Definition classical_basic_rules := [ excluded_middle ].
    Definition classical_derived_rules :=
      [ double_negp_elim
      ; double_negp
      ; contrapositiveNN
      ; contrapositiveNP
      ; impp2orp
      ].
    Definition demorgan_basic_rules := [ weak_excluded_middle ].
    Definition demorgan_derived_rules := [ demorgan_negp_andp ].
    Definition godeldummett_basic_rules := [ impp_choice ].
  End ProofTheory.
End Propositional.
