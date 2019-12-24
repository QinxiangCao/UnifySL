Require Import GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import MinimunLogic.Syntax.
Require Import MinimunLogic.ProofTheory.Minimun.
Require Import PropositionalLogic.Syntax.
Require Import PropositionalLogic.ProofTheory.Intuitionistic.
Require Import PropositionalLogic.ProofTheory.Classical.
Require Import PropositionalLogic.ProofTheory.DeMorgan.
Require Import PropositionalLogic.ProofTheory.GodelDummett.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Require Logic.LogicGenerator.ConfigLang.
Require Import Logic.LogicGenerator.Utils. 

Module C.
Import ConfigLang.
Import ListNotations.

Definition types: list type :=
  [ expr
  ; context
  ].

Definition connectives: list connective :=
  [ impp
  ; andp
  ; orp
  ; negp
  ; falsep
  ; truep
  ; sepcon
  ; wand
  ; emp
  ; multi_imp
  ; empty_context
  ].

Definition judgements: list judgement :=
  [ provable
  ; derivable
  ].

Definition how_types: list how_type :=
  [ FROM_ensemble_expr_TO_context
  ].

Definition how_connectives: list how_connective :=
  [ FROM_andp_impp_TO_iffp
  ; FROM_falsep_impp_TO_negp
  ; FROM_falsep_impp_TO_truep
  ; FROM_impp_TO_multi_imp
  ; FROM_empty_set_TO_empty_context
  ].

Definition how_judgements: list how_judgement :=
  [ FROM_provable_TO_derivable
  ; FROM_derivable_TO_provable
  ].

Definition type_classes :=
  [ Language
  ].

Definition connective_classes :=
  [ MinimumLanguage
  ; PropositionalLanguage
  ; SeparationLanguage
  ; EmpSeparationLanguage
  ].

Definition judgement_classes :=
  [ Provable
  ; Derivable
  ].

Definition rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_de_morgan
  ; provability_OF_godel_dummett
  ; provability_OF_classical_logic
  ; provability_OF_separation_logic
  ; provability_OF_emp_rule
  ; provability_OF_garbage_collected_sl
  ; derivitive_OF_impp
  ; derivitive_OF_propositional_connectives
  ; derivitive_OF_finite_derivation
(*  ; derivitive_OF_de_morgan *)
(*  ; derivitive_OF_godel_dummett *)
  ; derivitive_OF_classical_logic
  ; GEN_derivable_FROM_provable
  ; GEN_provable_FROM_derivable
  ].

End C.

Module PreList.
Import NameListNotations.
Section PreList.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL : SeparationLanguage L}
        {empL: SeparationEmpLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {SC : NormalSequentCalculus L GammaP GammaD}
        {minAX: MinimunAxiomatization L GammaP}
        {ipAX: IntuitionisticPropositionalLogic L GammaP}
        {cpAX: ClassicalPropositionalLogic L GammaP}
        {dmpAX: DeMorganPropositionalLogic L GammaP}
        {gdpAX: GodelDummettPropositionalLogic L GammaP}
        {sAX: SeparationLogic L GammaP}
        {empsAX: EmpSeparationLogic L GammaP}
        {extsAX: ExtSeparationLogic L GammaP}
        {nsesAX: NonsplitEmpSeparationLogic L GammaP}
        {desAX: DupEmpSeparationLogic L GammaP}
        {mfsAX: MallocFreeSeparationLogic L GammaP}
        {gcsAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimunSequentCalculus L GammaD}
        {ipSC : IntuitionisticPropositionalSequentCalculus L GammaD}
        {cpSC : ClassicalPropositionalSequentCalculus L GammaD}
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
  ; multi_imp
  ; empty_context
  ].

Definition judgements: list Name :=
  [ provable
  ; derivable
  ].

Definition how_types: list Name :=
  [ (context, expr -> Prop)
  ].

Definition how_connectives: list Name :=
  [ (iffp, fun x y => andp (impp x y) (impp y x))
  ; (negp, fun x => impp x falsep)
  ; (truep, impp falsep falsep)
  ; (multi_imp, fun xs y => fold_right impp y xs)
  ; (empty_context, Empty_set expr)
  ].

Definition how_judgements: list Name :=
  [ (derivable, fun Phi x => exists xs, Forall Phi xs /\ provable (multi_imp xs x))
  ; (provable, fun x => derivable empty_context x)
  ].

Definition Build_Language := Build_Language.
Definition Build_MinimunLanguage := Build_MinimunLanguage.
Definition Build_PropositionalLanguage := Build_PropositionalLanguage.
Definition Build_SeparationLanguage := Build_SeparationLanguage.
Definition Build_SeparationEmpLanguage := Build_SeparationEmpLanguage.
Definition Build_Provable := Build_Provable.
Definition Build_MinimunAxiomatization := Build_MinimunAxiomatization.
Definition Build_IntuitionisticPropositionalLogic := Build_IntuitionisticPropositionalLogic.
Definition Build_DeMorganPropositionalLogic := Build_DeMorganPropositionalLogic.
Definition Build_ClassicalPropositionalLogic := Build_ClassicalPropositionalLogic.
Definition Build_SeparationLogic := Build_SeparationLogic.
Definition Build_EmpSeparationLogic := Build_EmpSeparationLogic.
Definition Build_GarbageCollectSeparationLogic := Build_GarbageCollectSeparationLogic.
Definition Build_MinimunSequentCalculus := Build_MinimunSequentCalculus.
Definition Build_IntuitionisticPropositionalSequentCalculus := Build_IntuitionisticPropositionalSequentCalculus.
Definition Build_FiniteWitnessedSequentCalculus := Build_FiniteWitnessedSequentCalculus.

Definition type_instances_build :=
  [ (L, Build_Language expr)
  ].

Definition connective_instances_build :=
  [ (minL, Build_MinimunLanguage L impp)
  ; (pL, Build_PropositionalLanguage L andp orp falsep)
  ; (sL, Build_SeparationLanguage L sepcon wand)
  ; (empL, Build_SeparationEmpLanguage L _ emp)
  ].

Definition judgement_instances_build :=
  [ (GammaP, Build_Provable _ provable)
  ; (GammaD, Build_Derivable _ derivable)
  ].

Definition rule_instances_build :=
  [ (minAX, Build_MinimunAxiomatization L minL GammaP modus_ponens axiom1 axiom2)
  ; (ipAX, Build_IntuitionisticPropositionalLogic L minL pL GammaP minAX andp_intros andp_elim1 andp_elim2 orp_intros1 orp_intros2 orp_elim falsep_elim)
  ; (dmpAX, Build_DeMorganPropositionalLogic L minL pL GammaP minAX ipAX weak_excluded_middle)
  ; (gdpAX, Build_GodelDummettPropositionalLogic L minL pL GammaP minAX ipAX impp_choice)
  ; (cpAX, Build_ClassicalPropositionalLogic L minL pL GammaP minAX ipAX excluded_middle)
  ; (sAX, Build_SeparationLogic L minL pL sL GammaP minAX ipAX sepcon_comm_impp sepcon_assoc wand_sepcon_adjoint)
  ; (empsAX, Build_EmpSeparationLogic L minL pL sL empL GammaP minAX ipAX sAX sepcon_emp)
  ; (gcsAX, Build_GarbageCollectSeparationLogic L minL pL sL GammaP minAX ipAX sAX sepcon_elim1)
  ; (minSC, Build_MinimunSequentCalculus L minL GammaD deduction_modus_ponens deduction_impp_intros) 
  ; (ipSC, Build_IntuitionisticPropositionalSequentCalculus L pL GammaD deduction_andp_intros deduction_andp_elim1 deduction_andp_elim2 deduction_orp_intros1 deduction_orp_intros2 deduction_orp_elim deduction_falsep_elim)
  ; (fwSC, Build_FiniteWitnessedSequentCalculus L GammaD derivable_finite_witnessed)
  ; (cpSC, Build_ClassicalPropositionalSequentCalculus L minL pL GammaD bSC minSC ipSC derivable_excluded_middle)
  ; (AX, Build_NormalAxiomatization L minL GammaP GammaD derivable_provable)
  ; (SC, Build_NormalSequentCalculus L GammaP GammaD provable_derivable)
  ].

Ltac map_fst_tac x :=
  match x with
  | nil => constr:(@nil Name)
  | cons (BuildName (pair ?A ?B)) ?y =>
    let res := map_fst_tac y in
    constr:(cons (BuildName A) res)
  end.

Definition type_instances: list Name :=
  map_fst type_instances_build.

Definition connective_instances :=
  map_fst connective_instances_build.

Definition judgement_instances :=
  map_fst judgement_instances_build.

Definition rule_instances :=
  map_fst rule_instances_build.

Definition instances :=
  ltac:(let instances := eval cbv [type_instances connective_instances judgement_instances rule_instances app] in (type_instances ++ connective_instances ++ judgement_instances ++ rule_instances) in exact instances).

(* TODO maybe not manually *)
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

Definition classes_transition :=
  [ (GammaD, Provable2Derivable)
  ; (AX, Provable2Derivable_Normal)
  ; (SC, Axiomatization2SequentCalculus_SC)
  ; (bSC, Axiomatization2SequentCalculus_bSC)
  ; (fwSC, Axiomatization2SequentCalculus_fwSC)
  ; (minSC, Axiomatization2SequentCalculus_minSC)
  ].

End PreList.
End PreList.
