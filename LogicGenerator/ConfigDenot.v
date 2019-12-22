Require Import GeneralLogic.Base.
Require Import MinimunLogic.Syntax.
Require Import MinimunLogic.ProofTheory.Minimun.
Require Import PropositionalLogic.Syntax.
Require Import PropositionalLogic.ProofTheory.Intuitionistic.
Require Import PropositionalLogic.ProofTheory.Classical.
Require Import PropositionalLogic.ProofTheory.DeMorgan.
Require Import PropositionalLogic.ProofTheory.GodelDummett.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Require Import Utils. Import NameListNotations.

Module PreList.
Section PreList.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL : SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimunAxiomatization L GammaP}
        {ipGamma: IntuitionisticPropositionalLogic L GammaP}
        {cpGamma: ClassicalPropositionalLogic L GammaP}
        {dmpGamma: DeMorganPropositionalLogic L GammaP}
        {gdpGamma: GodelDummettPropositionalLogic L GammaP}
        {sGamma: SeparationLogic L GammaP}
        {empGamma: EmpSeparationLogic L GammaP}
        {extGamma: ExtSeparationLogic L GammaP}
        {nseGamma: NonsplitEmpSeparationLogic L GammaP}
        {deGamma: DupEmpSeparationLogic L GammaP}
        {mfGamma: MallocFreeSeparationLogic L GammaP}
        {gcGamma: GarbageCollectSeparationLogic L GammaP}
        .

Definition types: list Name :=
  [ expr
  ; context
  ].

Definition connectives: list Name :=
  [ impp
  ; andp
  ; orp
  ; negp
  ; falsep
  ; truep
  ; sepcon
  ; wand
  ; emp
  ].

Definition judgements: list Name :=
  [ provable
  ; derivable
  ].      

Definition primary_rules: list Name :=
  [ modus_ponens
  ; axiom1
  ; axiom2
  ; andp_intros
  ; andp_elim1
  ; andp_elim2
  ; orp_intros1
  ; orp_intros2
  ; orp_elim
  ; falsep_elim
  ; excluded_middle
  ; weak_excluded_middle
  ; demorgan_negp_andp
  ; impp_choice
  ; sepcon_comm_impp
  ; sepcon_assoc
  ; wand_sepcon_adjoint
  ].

Definition derived_rules :=
  [ provable_impp_refl
  ; provable_impp_arg_switch
  ; provable_impp_trans
  ; provable_multi_imp_shrink
  ; provable_multi_imp_arg_switch1
  ; provable_multi_imp_arg_switch2
  ; provable_add_multi_imp_left_head
  ; provable_add_multi_imp_left_tail
  ; provable_multi_imp_modus_ponens
  ; provable_multi_imp_weaken
  ; demorgan_orp_negp
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
  ; double_negp_elim
  ; double_negp
  ; contrapositiveNN
  ; contrapositiveNP
  ; impp2orp
  ; sepcon_orp_distr_l
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

End PreList.
End PreList.
