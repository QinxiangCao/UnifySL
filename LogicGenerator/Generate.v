Require Import Coq.Lists.List.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigDenot.
Require Import Logic.LogicGenerator.ConfigCompute.
Require Logic.LogicGenerator.ConfigLang.

Require Config.

Section Generate.
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
        {empAX: EmpSeparationLogic L GammaP}
        {extAX: ExtSeparationLogic L GammaP}
        {nseAX: NonsplitEmpSeparationLogic L GammaP}
        {deAX: DupEmpSeparationLogic L GammaP}
        {mfAX: MallocFreeSeparationLogic L GammaP}
        {gcAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimunSequentCalculus L GammaD}
        {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}
        {cpSC: ClassicalPropositionalSequentCalculus L GammaD}
        .
        
Import NameListNotations.

Definition foo :=
  ltac:(
    let res := eval compute in
    (ConfigCompute.result
       Config.how_connectives
       Config.how_judgements
       Config.transparent_names
       Config.primitive_rule_classes)
    in exact res).

Definition primitive_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.primitive_types foo).

Definition transparent_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.transparent_types foo).
  
Definition derived_types: list Name :=
  map_with_hint
    (ConfigDenot.D.how_types, ConfigDenot.S.how_types)
    (ConfigLang.Output.derived_types foo).
  
Definition primitive_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.primitive_connectives foo).

Definition transparent_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.transparent_connectives foo).

Definition derived_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.how_connectives, ConfigDenot.S.how_connectives)
    (ConfigLang.Output.derived_connectives foo).

Definition primitive_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.primitive_judgements foo).

Definition transparent_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.transparent_judgements foo).

Definition derived_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.how_judgements, ConfigDenot.S.how_judgements)
    (ConfigLang.Output.derived_judgements foo).

Definition aux_primitive_instances: list Name :=
  map_with_hint
    (ConfigDenot.D.classes, ConfigDenot.S.instances_build)
    (ConfigLang.Output.primitive_classes foo).

Definition aux_refl_instances_for_derivation: list Name :=
  map_with_hint
    (ConfigDenot.D.refl_classes, ConfigDenot.S.refl_instances)
    (ConfigLang.Output.refl_classes_for_derivation foo).

Definition aux_derived_instances: list Name :=
  map_with_hint
    (ConfigDenot.S.D_instance_transitions, ConfigDenot.S.instance_transitions)
    (ConfigLang.Output.derived_classes foo).

(* TODO: should be derived automatically *)
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
  ; provable_proper_iffp
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

Definition derived_instances :=
  [ provable_proper_iffp
  ].

Import ListNotations.

Inductive PrintType := IPar (Inline_list: list Name) | Axm | Der | Def | AIns | DIns.

Ltac print prt name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T =>
      match prt with
      | IPar ?l =>
        let should_inline := in_name_list n l in
        match should_inline with
        | true => idtac "  Parameter Inline" n ":" T "."
        | false => idtac "  Parameter" n ":" T "."
        end
      | Axm => idtac "  Axiom" n ":" T "."
      | Der => match n with
               | (?n0, ?n1) => idtac "  Definition" n0 ":=" n1 "."
               end
      | Def => idtac "  Definition" n ":" T ":=" n "."
      | AIns => match n with
                | (?n0, ?n1) =>
                  match type of n0 with
                  | ?T0 => idtac "  Instance" n0 ":" T0 ":=" n1 "."
                  end
                end
      | DIns => idtac "  Existing Instance" n "."
      end
    end
  end.

Ltac newline := idtac "".

Set Printing Width 1000.

Ltac two_stage_print :=
  let primitive_types := eval unfold primitive_types in primitive_types in
  let transparent_types := eval unfold transparent_types in transparent_types in
  let derived_types := eval unfold derived_types in derived_types in
  let primitive_connectives := eval unfold primitive_connectives in primitive_connectives in
  let transparent_connectives := eval unfold transparent_connectives in transparent_connectives in
  let derived_connectives := eval unfold derived_connectives in derived_connectives in
  let primitive_judgements := eval unfold primitive_judgements in primitive_judgements in
  let transparent_judgements := eval unfold transparent_judgements in transparent_judgements in
  let derived_judgements := eval unfold derived_judgements in derived_judgements in
(*  let := eval unfold in in *)

  idtac "Require Import Coq.Lists.List.";
  idtac "Require Import Coq.Sets.Ensembles.";

  newline;

  idtac "Module Type LanguageSig.";
  dolist (print (IPar transparent_types)) primitive_types;
  dolist (print Der) derived_types;
  dolist (print (IPar transparent_judgements)) primitive_judgements;
  dolist (print (IPar transparent_connectives)) primitive_connectives;
  idtac "End LanguageSig.";

  newline;

  idtac "Module DerivedNames (Names: LanguageSig).";
  idtac "  Import Names.";
  dolist (print Der) derived_connectives;
  dolist (print Der) derived_judgements;
  idtac "End DerivedNames.";

  newline;

  idtac "Module Type PrimitiveRuleSig (Names: LanguageSig).";
  idtac "Import Names.";
  idtac "Include DerivedNames (Names).";
  dolist (print Axm) primary_rules;
  idtac "End PrimitiveRuleSig.";

  newline;

  idtac "Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).";
  idtac "  Include Rules.";
  idtac "  Import Names Rules.";
  dolist (print Axm) derived_rules;
  dolist (print DIns) derived_instances;
  idtac "End LogicTheoremSig.";

  newline;

  idtac "Require Import Logic.GeneralLogic.Base.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  idtac "Require Import Logic.MinimunLogic.Syntax.";
  idtac "Require Import Logic.MinimunLogic.ProofTheory.Minimun.";
  idtac "Require Import Logic.PropositionalLogic.Syntax.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.Classical.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.";
  idtac "Require Import Logic.SeparationLogic.Syntax.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.";

  newline;

  idtac "Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names): LogicTheoremSig Names Rules.";
  idtac "  Import Names Rules.";
  idtac "  Include Rules.";
  dolist (print AIns) aux_primitive_instances;
  dolist (print AIns) aux_refl_instances_for_derivation;
  dolist (print AIns) aux_derived_instances;
  dolist (print Def) derived_rules;
  dolist (print DIns) derived_instances;
  idtac "End LogicTheorem.";

  newline;

  idtac "Require Logic.PropositionalLogic.DeepEmbedded.Solver.";
  idtac "Module IPSolver (Names: LanguageSig).";
  idtac "  Import Names.";
  idtac "  Ltac ip_solve :=";
  idtac "    change expr with Base.expr;";
  idtac "    change provable with Base.provable;";
  idtac "    change impp with Syntax.impp;";
  idtac "    change andp with Syntax.andp;";
  idtac "    intros; Solver.SolverSound.ipSolver.";
  idtac "End IPSolver.";



  
  idtac.



  
Goal False.
  two_stage_print.
Abort.

End Generate.
