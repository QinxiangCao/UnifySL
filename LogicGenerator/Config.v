Require Import LogicGenerator.Utils.
Require Import MinimunLogic.Syntax.
Require Import GeneralLogic.Base.
Require Import MinimunLogic.ProofTheory.Minimun.
Require Import PropositionalLogic.Syntax.
Require PropositionalLogic.ProofTheory.Intuitionistic.
Require PropositionalLogic.ProofTheory.Classical.
Require Import Coq.Lists.List.

Definition minimum := true.
Definition propositional := false.

Import ListNotations.
Module Minimum.
  Section Syntax.
    Context {L : Base.Language}
            {minL : MinimunLanguage L}.
    Definition connectives := [ BuildName impp ].
  End Syntax.

  Section ProofTheory.
    Context {L : Language}
            {minL : MinimunLanguage L}
            {Gamma : ProofTheory L}
            {minAx : MinimunAxiomatization L Gamma}.
    Definition basic_rules :=
      [ BuildName modus_ponens
      ; BuildName axiom1
      ; BuildName axiom2
      ].
    Definition derived_rules :=
      [ BuildName provable_impp_refl
      ; BuildName provable_impp_arg_switch
      ].
  End ProofTheory.
End Minimum.

Module Propositional.
  Section Syntax.
    Context {L : Language}
            {pL : PropositionalLanguage L}.
    Definition connectives :=
      [ BuildName andp
      ; BuildName orp
      ; BuildName falsep
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
      [ BuildName andp_intros
      ; BuildName andp_elim1
      ; BuildName andp_elim2
      ; BuildName orp_intros1
      ; BuildName orp_intros2
      ; BuildName orp_elim
      ; BuildName falsep_elim
      ].
    Definition intuitionistic_derived_rules :=
      [ BuildName andp_comm
      ; BuildName andp_assoc
      ].
    Definition classical_basic_rules := [ BuildName excluded_middle ].
    Definition classical_derived_rules :=
      [ BuildName double_negp_elim
      ; BuildName double_negp
      ].
    Definition demorgan_basic_rules := [ BuildName weak_excluded_middle ].
    Definition godeldummett_basic_rules := [ BuildName impp_choice ].
  End ProofTheory.
End Propositional.