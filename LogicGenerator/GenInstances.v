Require Import LogicGenerator.Utils.
Require LogicGenerator.Config.

Goal False.
  let minimum := eval cbv in Config.minimum in
  let propositional := eval cbv in Config.propositional in

  idtac "Require Import Logic.GeneralLogic.Base.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  when minimum: (
    idtac "Require Import Logic.MinimunLogic.Syntax.";
    idtac "Require Import Logic.MinimunLogic.ProofTheory.Minimun."
  );
  idtac "Module MakeInstances (Lang : LanguageSig) (Lgc : LogicSig Lang).";
  idtac "Import Lang Lgc.";
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
  idtac "End MakeInstances.".
Abort.
