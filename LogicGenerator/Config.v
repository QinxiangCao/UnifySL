Require Import LogicGenerator.Utils.
Require Import MinimunLogic.Syntax.
Require Import GeneralLogic.Base.
Require Import MinimunLogic.ProofTheory.Minimun.
Require Import PropositionalLogic.Syntax.
Require Import PropositionalLogic.ProofTheory.Intuitionistic.
Require Import PropositionalLogic.ProofTheory.Classical.
Require Import PropositionalLogic.ProofTheory.DeMorgan.
Require Import PropositionalLogic.ProofTheory.GodelDummett.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Definition minimum := true.
Definition propositional_intuitionistic := true.
Definition propositional_classical := false.
Definition propositional_demorgan := false.
Definition propositional_godeldummett := false.
Definition separation := true.

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

Module Separation.
  Section Syntax.
    Context {L : Language}
            {sL : SeparationLanguage L}
            {s'L : SeparationEmpLanguage L}.
    Definition connectives :=
      [ sepcon
      ; wand
      ].
    Definition emp_connectives :=
      [ emp
      ].
  End Syntax.

  Section ProofTheory.
    Context {L : Language}
            {minL : MinimunLanguage L}
            {pL : PropositionalLanguage L}
            {sL : SeparationLanguage L}
            {s'L : SeparationEmpLanguage L}
            {Gamma : ProofTheory L}
            {minAx : MinimunAxiomatization L Gamma}
            {ipGamma: IntuitionisticPropositionalLogic L Gamma}
            {sGamma: SeparationLogic L Gamma}
            {empGamma: EmpSeparationLogic L Gamma}
            {extGamma: ExtSeparationLogic L Gamma}
            {nseGamma: NonsplitEmpSeparationLogic L Gamma}
            {deGamma: DupEmpSeparationLogic L Gamma}
            {mfGamma: MallocFreeSeparationLogic L Gamma}
            {gcGamma: GarbageCollectSeparationLogic L Gamma}
            .
    Definition separation_basic_rules :=
      [ sepcon_comm_impp
      ; sepcon_assoc
      ; wand_sepcon_adjoint
      ].
    Definition separation_derived_rules :=
      [ sepcon_orp_distr_l
      ; falsep_sepcon
      ; provable_wand_sepcon_modus_ponens1
      ; wand_andp
      ; sepcon_comm
      ; sepcon_orp_distr_r
      ; sepcon_falsep
      ; provable_wand_sepcon_modus_ponens2
      ; wand_mono
      ; orp_wand
      ; sepcon_mono
      ].
  End ProofTheory.
End Separation.
