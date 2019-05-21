Require Import LogicGenerator.Utils.
Require LogicGenerator.Config.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.

Section Generate.
Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL : SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {dmpGamma: DeMorganPropositionalLogic L Gamma}
        {gdpGamma: GodelDummettPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {empGamma: EmpSeparationLogic L Gamma}
        {extGamma: ExtSeparationLogic L Gamma}
        {nseGamma: NonsplitEmpSeparationLogic L Gamma}
        {deGamma: DupEmpSeparationLogic L Gamma}
        {mfGamma: MallocFreeSeparationLogic L Gamma}
        {gcGamma: GarbageCollectSeparationLogic L Gamma}
        .

Inductive PrintType := Par | Axm | Def | Emp.

Ltac print prt name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T =>
      match prt with
      | Par => idtac "  Parameter" n ":" T "."
      | Axm => idtac "  Axiom" n ":" T "."
      | Def => idtac "  Definition" n ":" T ":=" n "."
      | Emp => idtac "  Definition" n ":= (* Fill in here *) ."
      end
    end
  end.

Ltac newline := idtac "".
Ltac print_unfold_name name :=
  match name with
  | BuildName ?ident =>
    idtac "  Ltac" ident ":= let e := eval unfold" ident "in" ident "in exact e.";
    idtac "  Notation" ident ":= ltac:(" ident ")."
  end.

Set Printing Width 1000.

Goal False.
  let minimum := eval cbv in Config.minimum in
  let propositional_intuitionistic := eval cbv in Config.propositional_intuitionistic in
  let separation := eval cbv in Config.separation in

  idtac "Module Type LanguageSig.";
  idtac "  Parameter Var : Type.";
  idtac "  Parameter expr : Type.";
  when minimum: (
       dolist (print Par) Config.Minimum.connectives;
       idtac "  Definition multi_imp xs y := fold_right impp y xs."
  );
  when propositional_intuitionistic: (
       dolist (print Axm) Config.Propositional.connectives;
       idtac "  Definition negp x := impp x falsep.";
       idtac "  Definition iffp x y := andp (impp x y) (impp y x).";
       idtac "  Definition truep := impp falsep falsep."
  );
  when separation:
       dolist (print Axm) Config.Separation.connectives;
  idtac "  Parameter provable : expr -> Prop.";
  when minimum:
       dolist (print Par) Config.Minimum.basic_rules;
  when propositional_intuitionistic:
       dolist (print Par) Config.Propositional.intuitionistic_basic_rules;
  when separation:
       dolist (print Par) Config.Separation.separation_basic_rules;
  idtac "End LanguageSig.";
  newline;

  idtac "Module Names <: LanguageSig.";
  idtac "  Definition Var := nat.";
  print Emp (BuildName expr);
  when minimum: (
       dolist (print Emp) Config.Minimum.connectives;
       idtac "  Definition multi_imp xs y := fold_right impp y xs."
  );
  when propositional_intuitionistic: (
       dolist (print Emp) Config.Propositional.connectives;
       idtac "  Definition negp x := impp x falsep.";
       idtac "  Definition iffp x y := andp (impp x y) (impp y x).";
       idtac "  Definition truep := impp falsep falsep."
  );
  when separation:
       dolist (print Emp) Config.Separation.connectives;
  print Emp (BuildName provable);
  when minimum:
       dolist (print Emp) Config.Minimum.basic_rules;
  when propositional_intuitionistic:
       dolist (print Emp) Config.Propositional.intuitionistic_basic_rules;
  when separation:
       dolist (print Emp) Config.Separation.separation_basic_rules;
  idtac "End Names.";
  newline;

  idtac "Module NamesNotation.";
  idtac "  Import Names.";
  dolist (print_unfold_name) Config.transparent_defs;
  idtac "End NamesNotation.";
  newline;

  idtac "Module Type LogicTheoremSig.";
  idtac "  Import Names NamesNotation.";
  when minimum: (
       dolist (print Axm) Config.Minimum.derived_rules;
       dolist (print Axm) Config.Minimum.multi_imp_derived_rules
  );
  when propositional_intuitionistic: (
       dolist (print Axm) Config.Propositional.intuitionistic_derived_rules
  );
  when separation:
       dolist (print Axm) Config.Separation.separation_derived_rules;
  idtac "End LogicTheoremSig.";
  newline;


  idtac "Require Import Logic.GeneralLogic.Base.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  when minimum: (
    idtac "Require Import Logic.MinimunLogic.Syntax.";
    idtac "Require Import Logic.MinimunLogic.ProofTheory.Minimun."
  );
  when propositional_intuitionistic: (
    idtac "Require Import Logic.PropositionalLogic.Syntax.";
    idtac "Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic."
  );
  when separation: (
    idtac "Require Import Logic.SeparationLogic.Syntax.";
    idtac "Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic."
  );


  idtac "Module MakeInstances.";
  idtac "  Import Names.";
  idtac "  Instance L : Language := Build_Language expr.";
  when minimum: (
    idtac "  Instance minL : MinimunLanguage L := Build_MinimunLanguage L impp.";
    idtac "  Instance G : ProofTheory L := Build_AxiomaticProofTheory provable.";
    idtac "  Instance AX : NormalAxiomatization L G := Build_AxiomaticProofTheory_AX provable.";
    idtac "  Instance minAX : MinimunAxiomatization L G := Build_MinimunAxiomatization L minL G modus_ponens axiom1 axiom2.";
    idtac "  Instance SC : NormalSequentCalculus L G := Axiomatization2SequentCalculus_SC.";
    idtac "  Instance bSC : BasicSequentCalculus L G := Axiomatization2SequentCalculus_bSC.";
    idtac "  Instance fwSC : FiniteWitnessedSequentCalculus L G := Axiomatization2SequentCalculus_fwSC.";
    idtac "  Instance minSC : MinimunSequentCalculus L G := Axiomatization2SequentCalculus_minSC."
  );
  when propositional_intuitionistic: (
    idtac "  Instance pL : PropositionalLanguage L := Build_PropositionalLanguage L andp orp falsep.";
    idtac "  Instance ipAX : IntuitionisticPropositionalLogic L G := Build_IntuitionisticPropositionalLogic L minL pL G minAX andp_intros andp_elim1 andp_elim2 orp_intros1 orp_intros2 orp_elim falsep_elim."
  );
  when separation: (
    idtac "  Instance sL: SeparationLanguage L := Build_SeparationLanguage L sepcon wand.";
    idtac "  Instance sAX: SeparationLogic L G := Build_SeparationLogic L minL pL sL G minAX ipAX sepcon_comm_impp sepcon_assoc wand_sepcon_adjoint."
  );
  idtac "End MakeInstances.";
  newline;

  idtac "Module LogicTheorem <: LogicTheoremSig.";
  idtac "  Import Names NamesNotation.";
  when minimum: (
       dolist (print Def) Config.Minimum.derived_rules;
       dolist (print Def) Config.Minimum.multi_imp_derived_rules
  );
  when propositional_intuitionistic:
       dolist (print Def) Config.Propositional.intuitionistic_derived_rules;
  when separation:
       dolist (print Def) Config.Separation.separation_derived_rules;
  idtac "End LogicTheorem.".

Abort.

End Generate.
