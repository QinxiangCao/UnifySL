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
  idtac "End LanguageSig.";

  idtac "Module Type LogicSig (L : LanguageSig).";
  idtac "Import L.";
  idtac "Parameter provable : expr -> Prop.";
  when minimum:
       dolist print_param Config.Minimum.basic_rules;
  when propositional:
       dolist print_param Config.Propositional.intuitionistic_basic_rules;
  idtac "End LogicSig.";

  idtac "Module Type LogicTheoremSig (L : LanguageSig) (Lg : LogicSig L).";
  idtac "Import L Lg.";
  when minimum:
       dolist print_axiom Config.Minimum.derived_rules;
  idtac "End LogicTheoremSig.".
Abort.

End Generate.