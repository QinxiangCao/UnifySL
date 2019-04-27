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

Section Generate.
Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {dmpGamma: DeMorganPropositionalLogic L Gamma}
        {gdpGamma: GodelDummettPropositionalLogic L Gamma}.

Ltac print_param name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T => idtac "Parameter" n ":" T "."
    end
  end.

Ltac print_axiom name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T => idtac "Axiom" n ":" T "."
    end
  end.

Ltac print_theorem name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T => idtac "Definition" n ":" T ":=" n "."
    end
  end.

Ltac print_empty_definition name :=
  match name with
  | BuildName ?n =>
    idtac "Definition" n ":= (* Fill in here *) ."
  end.

Goal False.
  let minimum := eval cbv in Config.minimum in
  let propositional := eval cbv in Config.propositional in

  idtac "Module Type LanguageSig.";
  idtac "Parameter Var : Type.";
  idtac "Parameter expr : Type.";
  when minimum:
       dolist print_param Config.Minimum.connectives;
  when propositional:
       dolist print_param Config.Propositional.connectives;
  idtac "Parameter provable : expr -> Prop.";
  when minimum:
       dolist print_param Config.Minimum.basic_rules;
  when propositional:
       dolist print_param Config.Propositional.intuitionistic_basic_rules;
  idtac "End LanguageSig.";

  idtac "Module Names <: LanguageSig.";
  idtac "Definition Var := nat.";
  print_empty_definition (BuildName expr);
  when minimum:
       dolist print_empty_definition Config.Minimum.connectives;
  when propositional:
       dolist print_empty_definition Config.Propositional.connectives;
  print_empty_definition (BuildName provable);
  when minimum:
       dolist print_empty_definition Config.Minimum.basic_rules;
  when propositional:
       dolist print_empty_definition Config.Propositional.intuitionistic_basic_rules;
  idtac "End Names.";

  idtac "Module NamesNotation.";
  idtac "Ltac expr := let e := eval unfold Names.expr in Names.expr in exact e.";
  idtac "Notation expr := ltac:(expr).";
  idtac "End NamesNotation.";

  idtac "Module Type LogicTheoremSig.";
  idtac "Import Names NamesNotation.";
  when minimum:
       dolist print_axiom Config.Minimum.derived_rules;
  idtac "End LogicTheoremSig.";


  idtac "Require Logic.GeneralLogic.Base.";
  idtac "Require Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  when minimum: (
    idtac "Require Logic.MinimunLogic.Syntax.";
    idtac "Require Logic.MinimunLogic.ProofTheory.Minimun."
  );

  idtac "Module MakeInstances.";
  idtac "Import Logic.GeneralLogic.Base.";
  idtac "Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  when minimum: (
    idtac "Import Logic.MinimunLogic.Syntax.";
    idtac "Import Logic.MinimunLogic.ProofTheory.Minimun."
  );
  idtac "Import Names.";
  idtac "Instance L : Language := Build_Language expr.";
  when minimum: (
    idtac "Instance minL : MinimunLanguage L := Build_MinimunLanguage L impp.";
    idtac "Instance G : ProofTheory L := Build_AxiomaticProofTheory provable.";
    idtac "Instance AX : NormalAxiomatization L G := Build_AxiomaticProofTheory_AX provable.";
    idtac "Instance minAX : MinimunAxiomatization L G := Build_MinimunAxiomatization L minL G modus_ponens axiom1 axiom2.";
    idtac "Instance SC : NormalSequentCalculus L G := Axiomatization2SequentCalculus_SC.";
    idtac "Instance bSC : BasicSequentCalculus L G := Axiomatization2SequentCalculus_bSC.";
    idtac "Instance fwSC : FiniteWitnessedSequentCalculus L G := Axiomatization2SequentCalculus_fwSC.";
    idtac "Instance minSC : MinimunSequentCalculus L G := Axiomatization2SequentCalculus_minSC."
  );
  idtac "End MakeInstances.";

  idtac "Module LogicTheorem <: LogicTheoremSig.";
  idtac "Import Logic.MinimunLogic.ProofTheory.Minimun.";
  idtac "Import Names NamesNotation.";
  when minimum:
       dolist print_theorem Config.Minimum.derived_rules;
  idtac "End LogicTheorem.".
  
Abort.

End Generate.
